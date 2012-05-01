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
  [B Int Bool ⊥]
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
     (mon h f g C E)]
  ; for type-checking
  [MaybeT T
          TypeError]
  [TEnv ((X T) ...)])


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


;; type checking

;; returns expression's type, or TypeError if doesn't work out
(define-metafunction CPCF
  type : M -> MaybeT
  [(type M) (type-check () M)])

;; works out expression's type from given type-environment
(define-metafunction CPCF
  type-check : TEnv M -> MaybeT
  [(type-check TEnv n) Int]
  [(type-check TEnv b) Bool]
  [(type-check ((X_0 T_0) ...) (λ (X T) M))
   (maybe→ T (type-check ((X T) (X_0 T_0) ...) M))]
  [(type-check TEnv (blame f g)) ⊥]
  [(type-check ((X_0 T_0) ... (X T) (X_1 T_1) ...) X)
   T
   (side-condition (not (member (term X) (term (X_0 ...)))))]
  [(type-check TEnv (M ...))
   (maybe-type-app (type-check TEnv M) ...)]
  [(type-check TEnv (μ (X T) M)) ⊥] ; TODO no idea
  [(type-check TEnv (if M ...))
   (maybe-type-if (type-check TEnv M) ...)]
  [(type-check TEnv (o M ...)) (∆ o (type-check TEnv M) ...)]
  [(type-check TEnv (mon h f g C M))
   (maybe-type-mon (type-check-con TEnv C) (type-check TEnv M))]
  [(type-check TEnv M) TypeError])

;; work's out contract's type from given type-environment
(define-metafunction CPCF
  type-check-con : TEnv C -> MaybeT
  [(type-check-con TEnv (flat M)) (maybe-flat (type-check TEnv M))]
  [(type-check-con TEnv (C ↦ D))
   (maybe-con→ (type-check-con TEnv C) (type-check-con TEnv D))]
  [(type-check-con ((X_0 T_0) ...) (C ↦ (λ (X T) D)))
   (maybe-con→ (type-check-con ((X_0 T_0) ...) C)
               (type-check-con ((X T) (X_0 T_0) ...) D))])

;; I wish redex had higher order functions =.=

;; constructs function type
(define-metafunction CPCF
  maybe→ : MaybeT MaybeT -> MaybeT
  [(maybe→ T_x T_y) (T_x → T_y)]
  [(maybe→ any_1 any_2) TypeError])

;; returns function application's type if it's legal
(define-metafunction CPCF
  maybe-type-app : MaybeT MaybeT -> MaybeT
  [(maybe-type-app (T_x → T_y) T)
   T_y
   (side-condition (term (⊑ T T_x)))]
  [(maybe-type-app any_1 any_2) TypeError])

;; returns if expessions' type if it's legal
(define-metafunction CPCF
  maybe-type-if : MaybeT MaybeT MaybeT -> MaybeT
  [(maybe-type-if T_test T_then T_else)
   (⊔ T_then T_else)
   (side-condition (term (⊑ T_test Bool)))]
  [(maybe-type-if any_1 any_2 any_3) TypeError])

;; returns monitor expression's type if it's legal
(define-metafunction CPCF
  maybe-type-mon : MaybeT MaybeT -> MaybeT
  [(maybe-type-mon (con T_c) T)
   T
   (side-condition (term (⊑ T T_c)))]
  [(maybe-type-mon any_1 any_2) TypeError])

;; returns flat contract's type if it's legal
(define-metafunction CPCF
  maybe-flat : MaybeT -> MaybeT
  [(maybe-flat (T → T_b))
   (con T)
   (side-condition (term (⊑ T_b Bool)))]
  [(maybe-flat any) TypeError])

;; returns function contract's type if it's legal
(define-metafunction CPCF
  maybe-con→ : MaybeT MaybeT -> MaybeT
  [(maybe-con→ (con T_x) (con T_y)) (con (T_x → T_y))]
  [(maybe-con→ any_1 any_2) TypeError])

;; types for primitive ops
(define-metafunction CPCF
  ∆ : o MaybeT ... -> MaybeT
  [(∆ o Int)
   Bool
   (side-condition (member (term o) (term (zero? even? odd?))))]
  [(∆ o Bool)
   Bool
   (side-condition (member (term o) (term (true? false?))))]
  [(∆ o Int Int)
   Int
   (side-condition (member (term o) (term (+ -))))]
  [(∆ o Bool Bool)
   Bool
   (side-condition (member (term o) (term (∨ ∧))))]
  [(∆ o any ...) TypeError])

;; subtype test
(define-metafunction CPCF
  ⊑ : T T -> any ;bool
  [(⊑ T T) #t]
  [(⊑ ⊥ T) #t]
  [(⊑ (T_x1 → T_y1) (T_x2 → T_y2))
   ,(and (term (⊑ T_x2 T_x1)) (term (⊑ T_y1 T_y2)))]
  [(⊑ (con T_1) (con T_2)) (⊑ T_1 T_2)]
  [(⊑ any_1 any_2) #f])

;; returns most specific supertype
(define-metafunction CPCF
  ⊔ : T T -> MaybeT
  [(⊔ T T) T]
  [(⊔ ⊥ T) T]
  [(⊔ T ⊥) T]
  ; ⊓ for function domains doesn't make practical sense in this language
  ; for simplicity, assume same domain
  [(⊔ (T → T_y1) (T → T_y2)) (T → (⊔ T_y1 T_y2))]
  [(⊔ (con T_1) (con T_2)) (con (⊔ T_1 T_2))]
  [(⊔ any_1 any_2) TypeError])


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
(test-equal (term (type ,t-even?)) (term (Int → Bool)))
(test-equal (term (type ,db1)) (term ((Int → Int) → (Int → Int))))
(test-equal (term (type ,ap0)) (term (Int → Int)))
(test-equal (term (type ,ap00)) (term Int))
(test-equal (term (type ,ap01)) (term Int))
(test-results)