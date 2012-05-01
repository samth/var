#lang racket
(require redex)

;; PCF with Contracts
(define-language CPCF
  ; terms
  [(M N L) A
           X
           (M M)
           (μ (X T) M)
           (if M M M)
           (o1 M)
           (o2 M M)
           ; h,f,g: original, positive, negative
           (mon h f g C M)]
  [(X Y Z f g h) variable-not-otherwise-mentioned]
  ; types
  [T B
     (T → T)
     (con T)]
  [B Int Bool]
  ; primitive ops
  [o o1 o2]
  [o1 zero? even? odd? true? false?]
  [o2 + - ∨ ∧]
  ; contracts
  [(C D) (flat M)
         (C ↦ C)
         (C ↦ (λ (X T) C))]
  ; answers
  [A V
     (blame f g)] ; f breaks its contract with g
  ; values
  [V (λ (X T) M)
     n
     b]
  [(m n) integer]
  [b tt ff]
  ; evaluation contexts
  [E hole
     (E M)
     (V E)
     (o V ... E M ...)
     (if E M M)
     (mon h f g C E)])
           
;; Semantics for CPCF
(define CPCF-red
  (reduction-relation
   CPCF
   (v (if tt M N) M
      if)
   (v (if ff M N) N
      if-not)
   (v ((λ (X T) M) V)
      (subst M X V)
      β)
   (v (μ (X T) M)
      (subst M X (μ (X T) M))
      μ)
   (v (o V ...)
      (δ o V ...)
      δ)
   (v (mon h f g (C ↦ D) V)
      (λ (X Int)
        ; X's type does not matter because program has type-checked
        ; at this point, and X will never be used
        (mon h f g D
             (V (mon h g f C X))))
      mon-fun-desugar
      (where X ,(variable-not-in (term (D V)) (term dummy))))
   (v (mon h f g (C ↦ (λ (X T) D)) V)
      (λ (X T)
        (mon h f g D
             (V (mon h g f C X))))
      mon-fun)
   (v (mon h f g (flat M) V)
      (if (M V) V (blame f h))
      mon-flat)
   ; because my definition for A is slightly different from the paper's
   (--> (in-hole E (blame f g))
        (blame f g)
        blame-prop
        (side-condition (not (equal? (term hole) (term E)))))
   with
   [(--> (in-hole E M) (in-hole E N)) (v M N)]))

;; capture-avoiding substitution
(define-metafunction CPCF
  ; the first one is 'any' so I can be slightly sloppy with 'if' and ops
  subst : any X M -> any
  [(subst (λ (X T) M) X N) (λ (X T) M)] ; var bound, so ignored
  [(subst (λ (X T) M) Y N)
   (λ (Z T)
     (subst (subst M X Z) Y N)) ; TODO: exponential blow-up risk
   (where Z ,(variable-not-in (term (M Y N)) (term X)))]
  [(subst X X M) M]
  [(subst (μ (X T) M) X N) (μ (X T) M)] ; var bound, so ignored
  [(subst (μ (X T) M) Y N)
   (μ (Z T)
      (subst (subst M X Z) Y N))] ; TODO: exponential blow-up risk
  [(subst (mon h f g C M) X N)
   (mon h f g (subst-con C X N) (subst M X N))]
  [(subst (any ...) X M) ((subst any X M) ...)]
  [(subst any X M) any])

;; capture-avoiding substitution for contracts
(define-metafunction CPCF
  subst-con : C X M -> C
  [(subst-con (flat M) X N) (flat (subst M X N))]
  [(subst-con (C ↦ D) X M) ((subst-con C X M) ↦ (subst-con D X M))]
  [(subst-con (C ↦ (λ (Y T) D)) X M)
   ((subst-con C X M)
    ↦ (λ (Z T)
        (subst-con (subst-con D Y Z) X M))) ; TODO: exp blow-up
   (where Z ,(variable-not-in (term (D X M)) (term Y)))])

;; interprets primitive ops
(define-metafunction CPCF
  δ : o V ... -> A
  [(δ zero? n) (to-bool ,(zero? (term n)))]
  [(δ even? n) (to-bool ,(even? (term n)))]
  [(δ odd? n) (to-bool ,(odd? (term n)))]
  [(δ true? b) (to-bool ,(equal? (term b) (term tt)))]
  [(δ false? b) (to-bool ,(equal? (term b) (term ff)))]
  [(δ + m n) ,(+ (term m) (term n))]
  [(δ - m n) ,(- (term m) (term n))]
  [(δ ∨ b ...) ,(ormap (curry equal? (term tt)) (term (b ...)))]
  [(δ ∧ b ...) ,(andmap (curry equal? (term tt)) (term (b ...)))])

;; converts racket's boolean to CPCF's boolean
(define-metafunction CPCF
  to-bool : any -> b
  [(to-bool #f) ff]
  [(to-bool any) tt])
                      
;; CPCF term examples + tests
(define t-even? (term (λ (x Int) (even? x))))
(define db1
  (term (mon h f g
             (((flat ,t-even?) ↦ (flat ,t-even?))
              ↦ ((flat ,t-even?) ↦ (flat ,t-even?)))
             (λ (f (Int → Int))
               (λ (x Int)
                 (f (f x)))))))
(define ap0 (term (,db1 (λ (x Int) 2))))
(define ap1 (term (,db1 (λ (x Int) 7))))
(define ap00 (term (,ap0 42)))
(define ap01 (term (,ap0 13)))
(define ap10 (term (,ap1 0)))
(test-->> CPCF-red ap00 2)
(test-->> CPCF-red ap01 (term (blame g h)))
(test-->> CPCF-red ap10 (term (blame g h)))
(test-results)