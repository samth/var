#lang racket
(require redex)

(define (all-but-last ls)
  (drop-right ls 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Languages

;; Figure 5.
(define-language λc-user
  (P (M ... E))
  (M (module f C V))
  (L (λ x E) (λ x x E))
  (W L)
  (bool #t #f)
  (V n bool W string) 
  (SV L (f ^ f)) ; Syntactic values for pred.  [Different than paper]
  (E V x (f ^ f) (E E f) (if E E E) (o1 E f) (o2 E E f) (let x E E) (begin E E))
  (C int/c any/c bool/c string/c none/c (C -> C) (pred SV))
  (x variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned o † ★) ;; † is top-level
  (n natural)
  (int natural)
  (o o1 o2)
  (o1 add1 sub1 zero? proc?)
  (o2 + - * expt = < <= > >=)
  (𝓔 hole (𝓔 E f) (V 𝓔 f) (if 𝓔 E E) (o V ... 𝓔 E ... f) (let x 𝓔 E) (begin 𝓔 E)))
  
;; Figure 5, gray (cont).
(define-extended-language λc λc-user
  (W .... ((C --> C) <= f f V f W))  
  (B (blame f f V C V))
  (E .... (C <= f f V f E) B)
  (C .... (C --> C) λ)
  (f .... Λ)
  (𝓔 .... (C <= f f V f 𝓔)))

;; Figure 5, gray (cont).
(define-extended-language λc~ λc
  (V .... (-- C C ...))                       ;; (-- X) is overline X.
  (B .... (blame f? g? V1? C? V2?))
  (M .... (module f C ☁))
  (W .... (-- (C -> C) C ...) (-- any/c C ...) (-- (pred SV) C ...))
  
  (W* L 
      ((C --> C) <= f f V f W*) 
      (-- C ... (C -> C) C ...))
  
  (aproc W*)
  (aint int (-- C ... int/c C ...))
  (astring string (-- C ... string/c C ...))
  (abool bool (-- C ... bool/c C ...)))

(define aint? (redex-match λc~ aint))
(define astring? (redex-match λc~ astring))
(define abool? (redex-match λc~ abool))
(define abstract-value? (redex-match λc~ (-- C ...)))
(define (final-state? x)
  (or (redex-match λc~ V x)
      (redex-match λc~ B x)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metafunctions

(define-metafunction λc~
  demonic : C -> L
  [(demonic any/c)
   (λ f x (if (proc? x ★) 
              (f (x (-- any/c) ★) ★)  ;; want to add fact that x is a proc.
              0))
   (where (f x) ,(list (gensym 'f) (gensym 'x)))]
  [(demonic (pred SV))
   (demonic any/c)]
  [(demonic int/c) (λ x 0)]
  [(demonic string/c) (λ x 0)]
  [(demonic bool/c) (λ x 0)]
  [(demonic none/c) (λ x 0)]
  ;; Maybe add blessed arrow contracts
  [(demonic (C_0 -> C_1)) 
   (λ f ((demonic C_1) (f (-- C_0) ★) ★))
   (where f ,(gensym 'f))])

;; FIXME: Don't handle abstract values
(define-metafunction λc~
  [(δ (add1 n f)) ,(add1 (term n))]
  [(δ (sub1 0 f)) 0]
  [(δ (sub1 n f)) ,(sub1 (term n))]
  [(δ (zero? n f)) ,(zero? (term n))]  
  [(δ (+ n_1 n_2 f)) ,(+ (term n_1) (term n_2))]
  [(δ (- n_1 n_2 f)) ,(max 0 (- (term n_1) (term n_2)))]
  [(δ (* n_1 n_2 f)) ,(* (term n_1) (term n_2))]
  [(δ (expt n_1 n_2 f)) ,(expt (term n_1) (term n_2))]
  [(δ (= n_1 n_2 f)) ,(= (term n_1) (term n_2))]
  [(δ (< n_1 n_2 f)) ,(< (term n_1) (term n_2))]
  [(δ (<= n_1 n_2 f)) ,(<= (term n_1) (term n_2))]
  [(δ (> n_1 n_2 f)) ,(> (term n_1) (term n_2))]  
  [(δ (>= n_1 n_2 f)) ,(>= (term n_1) (term n_2))]

  [(δ (proc? aproc f)) #t]
  [(δ (proc? (-- int/c C ...) f)) #f]
  [(δ (proc? (-- string/c C ...) f)) #f]
  [(δ (proc? (-- bool/c  C ...) f)) #f]
  ;[(δ (proc? (-- none/c  C ...) f)) ,(error "Really?")]
  [(δ (proc? (-- C C_0 ...) f)) (-- bool/c)]
  [(δ (proc? V f)) #f]
  
  [(δ (o1 V f)) (blame f o1 V λ V)]
  ;; FIXME: should refer to V_1 and V_2.
  [(δ (o2 V_1 V_2 f)) (blame f o2 V_1 λ V_1)])

(test-equal (term (δ (proc? #f f))) #f)
(test-equal (term (δ (add1 0 f))) 1)
(test-equal (term (δ (sub1 0 f))) 0)
(test-equal (term (δ (zero? 0 f))) #t)
(test-equal (term (δ (zero? 1 f))) #f)
(test-equal (term (δ (add1 #t f))) (term (blame f add1 #t λ #t)))

;; Test for δ totalness.
(redex-check λc~ (o1 V)
             (or (redex-match λc~ V (term (δ (o1 V f))))
                 (equal? (term (blame f o1 V λ V))
                         (term (δ (o1 V f))))))
(redex-check λc~ (o2 V_1 V_2)
             (or (redex-match λc~ V (term (δ (o2 V_1 V_2 f))))
                 (redex-match λc~ B (term (δ (o2 V_1 V_2 f))))))

(define-metafunction λc~ subst : x any any -> any  
  ;; 1. x bound, so don't continue in λ body  
  [(subst x any_1 (λ x any_2)) 
   (λ x any_2)] 
  [(subst x any_1 (λ x_0 x any_2))
   (λ x_0 x any_2)]
  [(subst x any_1 (λ x x_0 any_2))
   (λ x_0 x any_2)]
  [(subst x any_1 (let x any_2 any_3))
   (let x (subst x any_1 any_2) any_3)]
  ;; 2. general purpose capture avoiding case  
  [(subst x_1 any_1 (λ x_2 any_2)) 
   (λ x_new
     (subst x_1 any_1 (subst-var x_2 x_new any_2))) 
   (where x_new 
          ,(variable-not-in (term (x_1 any_1 any_2)) 
                            (term x_2)))] 
  [(subst x_1 any_1 (λ x_2 x_3 any_2)) 
   (λ x_new1 x_new2
     (subst x_1 any_1 (subst-var x_2 x_new1 (subst-var x_3 x_new2 any_2))))
   (where (x_new1 x_new2)
          (,(variable-not-in (term (x_1 x_3 any_1 any_2)) 
                             (term x_2))
           ,(variable-not-in (term (x_1 x_2 any_1 any_2)) 
                             (term x_3))))]
    [(subst x_1 any_1 (let x_2 any_2 any_3))
   (let x_new
     (subst x_1 any_1 any_2)
     (subst x_1 any_1 (subst-var x_2 x_new any_2)))   
   (where x_new 
          ,(variable-not-in (term (x_1 any_1 any_2)) 
                            (term x_2)))]
  
  ;; 3. replace x_1 with e_1  
  [(subst x_1 any_1 x_1) any_1]  
  ;; 4. x_1 and x_2 are different, so don't replace  
  [(subst x_1 any_1 x_2) x_2]  
  ;; the last cases cover all other expressions  
  [(subst x_1 any_1 (any_2 ...)) 
   ((subst x_1 any_1 any_2) ...)] 
  [(subst x_1 any_1 any_2) 
   any_2])

(define-metafunction λc~ subst-var : x any any -> any 
  [(subst-var x_1 any_1 x_1) any_1] 
  [(subst-var x_1 any_1 (any_2 ...)) 
   ((subst-var x_1 any_1 any_2) ...)] 
  [(subst-var x_1 any_1 any_2) any_2])

(test-equal (term (subst x 0 x)) (term 0))
(test-equal (term (subst x 0 y)) (term y))
(test-equal (term (subst x 0 (λ x x))) (term (λ x x)))

(define-metafunction λc~
  remember-contract : V C ... -> V
  [(remember-contract (-- C_0 ... C C_1 ...) C C_2 ...)
   (remember-contract (-- C_0 ... C C_1 ...) C_2 ...)]
  [(remember-contract (-- C_0 C_1 ...) C_2 ...)
   (-- C_0 C_2 ... C_1 ...)]
  [(remember-contract V C ...) V])

(define-metafunction λc~
  dom-contract : f (M ...) -> C
  [(dom-contract f (any_0 ... (module f (C_0 -> C_1) any) any_1 ...))
   C_0]
  [(dom-contract f any) any/c])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples and tests

;; Modified from Figure 8 in paper (8 -> #f).
(define example-8
  (term [(module f (any/c -> (any/c -> any/c)) (λ x x))
         (module g ((pred (λ x x)) -> int/c) (λ x 0))
         (module h any/c (λ z (((f ^ h) (g ^ h) h) #f h)))
         ((h ^ †) 0 †)]))

(define example-8-opaque
  (term [(module f (any/c -> (any/c -> any/c)) ☁)
         (module g ((pred (λ x x)) -> int/c) ☁)
         (module h any/c (λ z (((f ^ h) (g ^ h) h) #f h)))
         ((h ^ †) 0 †)]))

(test-predicate (redex-match λc-user M) (first example-8))
(test-predicate (redex-match λc-user M) (second example-8))
(test-predicate (redex-match λc-user M) (third example-8))
(test-predicate (redex-match λc-user E) (last example-8))
(test-predicate (redex-match λc~ P) example-8-opaque)
(test-predicate (redex-match λc-user P) example-8)
(test-predicate (redex-match λc P) example-8)
(test-predicate (redex-match λc~ P) example-8)

(test-predicate (redex-match λc-user C) (term ((pred (λ x x)) -> int/c)))

(define fit-example
  (term [(module prime? (int/c -> any/c) ☁)
         (module rsa ((pred (prime? ^ rsa)) -> (string/c -> string/c)) ☁)
         (module keygen (any/c -> (pred (prime? ^ keygen))) ☁)
         (((rsa ^ †) ((keygen ^ †) #f †) †) "Plain" †)]))

(define fit-example-rsa-7
  (term [(module prime? (int/c -> any/c) ☁)
         (module rsa ((pred (prime? ^ rsa)) -> (string/c -> string/c)) ☁)
         (module keygen (any/c -> (pred (prime? ^ keygen))) (λ x 7))
         (((rsa ^ †) ((keygen ^ †) #f †) †) "Plain" †)]))

;; Should see keygen break contract with prime?.
(define fit-example-keygen-string
  (term [(module prime? (int/c -> any/c) ☁)
         (module rsa ((pred (prime? ^ rsa)) -> (string/c -> string/c)) ☁)
         (module keygen (any/c -> (pred (prime? ^ keygen))) (λ x "Key"))
         (((rsa ^ †) ((keygen ^ †) #f †) †) "Plain" †)]))

(define fit-example-alt
  (term [(module prime? (int/c -> any/c) ☁)
         (module rsa (string/c -> ((pred (prime? ^ rsa)) -> string/c)) ☁)
         (module keygen (any/c -> (pred (prime? ^ keygen))) ☁)
         (((rsa ^ †) "Plain" †) ((keygen ^ †) #f †) †)]))

(test-predicate (redex-match λc~ P) fit-example)
(test-predicate (redex-match λc~ P) fit-example-alt)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relations

(define v
  (reduction-relation
   λc~ #:domain E
   (--> ((λ x E) V f) (subst x V E) β)
   (--> ((λ x_0 x_1 E) V f) (subst x_0 (λ x_0 x_1 E) (subst x_1 V E)) β-rec)
   (--> (n V f) (blame f Λ n λ n) wrong)
   (--> (if V E_1 E_2) E_1 
        (side-condition (term V))
        if-t)
   (--> (if V E_1 E_2) E_2 
        (side-condition (not (term V)))
        if-f)   
   (--> (o V ... f)
        (δ (o V ... f))
        δ)   
   (--> (begin V E) E begin)
   (--> (let x V E)
        (subst x V E) let)))
   
(test--> v (term ((λ x 0) 1 †)) (term 0))
(test--> v 
         (term ((λ f x (f x †)) 0 †))
         (term ((λ f x (f x †)) 0 †)))                 
(test--> v (term (0 1 †)) (term (blame † Λ 0 λ 0)))
(test--> v (term (if 0 1 2)) (term 1))
(test--> v (term (if #t 1 2)) (term 1))
(test--> v (term (if #f 1 2)) (term 2))
(test--> v (term (add1 0 †)) 1)
(test--> v (term (proc? #f †)) #f)

(define c
  (reduction-relation
   λc~ #:domain E
   (--> (((C_1 --> C_2) <= f_1 f_2 V_1 f_3 W) V_2 f_4)
        (C_2 <= f_1 f_2 V_1 f_3 (W (C_1 <= f_2 f_1 V_2 f_3 V_2) f_4))
        split)   
   (--> (int/c <= f_1 f_2 V f_3 aint) 
        (remember-contract aint int/c) 
        chk-int-pass)
   (--> (int/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 int/c V_2)
        (side-condition (not (aint? (term V_2))))
        chk-int-fail)
   (--> (none/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 none/c V_2)
        chk-none-fail)
   (--> (string/c <= f_1 f_2 V f_3 astring) 
        (remember-contract astring string/c)
        chk-string-pass)   ;; new
   (--> (string/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 string/c V_2)
        (side-condition (not (astring? (term V_2))))
        chk-string-fail)   
   (--> (bool/c <= f_1 f_2 V f_3 abool)
        (remember-contract abool bool/c)
        chk-bool-pass)   ;; new
   (--> (bool/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 bool/c V_2)
        (side-condition (not (abool? (term V_2))))
        chk-bool-fail)   
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 W)
        ((C_1 --> C_2) <= f_1 f_2 V f_3 W)
        chk-fun-pass)
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 n)
        (blame f_1 f_3 V (C_1 -> C_2) n)
        chk-fun-fail)
      
   (--> ((pred SV) <= f_1 f_2 V_1 f_3 V_2)
        (if (SV V_2 Λ) 
            (remember-contract V_2 (pred SV))
            (blame f_1 f_3 V_1 (pred SV) V_2))
        ;; Only want smart to fire when condition holds
        (side-condition 
         (not (redex-match λc~ 
                           ((pred (f_a ^ f_b)) <= f_1* f_2* V_* f_3* (-- C_0 ... (pred (f_a ^ f_c)) C_1 ...))
                           (term ((pred SV) <= f_1 f_2 V_1 f_3 V_2)))))
        chk-pred-c)   
   
   ;; sugar
   (--> (any/c <= f_1 f_2 V_1 f_3 V_2) V_2 any-pass)))

(test--> c 
         (term (((any/c --> any/c) <= f g 7 f (λ x 5)) 8 †))
         (term (any/c <= f g 7 f ((λ x 5) (any/c <= g f 8 f 8) †))))
(test--> c (term (int/c <= f g 0 f 5)) (term 5))
(test--> c 
         (term (int/c <= f g 0 f (λ x x))) 
         (term (blame f f 0 int/c (λ x x))))
(test--> c 
         (term (int/c <= f g 0 f #t)) 
         (term (blame f f 0 int/c #t)))
(test--> c
         (term ((any/c  -> any/c) <= f g 0 f (λ x x)))
         (term ((any/c --> any/c) <= f g 0 f (λ x x))))
(test--> c 
         (term ((any/c  -> any/c) <= f g 0 f 5))
         (term (blame f f 0 (any/c -> any/c) 5)))
(test--> c
         (term ((pred (λ x 0)) <= f g 0 f 5))
         (term (if ((λ x 0) 5 Λ)
                   5
                   (blame f f 0 (pred (λ x 0)) 5))))

(define c~
  (reduction-relation
   λc~ #:domain E
   ;; IMPROVE ME: for all (C_1 -> C_2) in C ..., you know C_2 of result.
   (--> ((-- (pred SV) C ...) V f)
        (begin ((demonic (pred SV)) V ★) (-- any/c))
        (side-condition (not (abstract-value? (term V))))
        apply-abs-pred-concrete)
   (--> ((-- (pred SV) C ...) (-- C_0 ...) f)
        (-- any/c)
        apply-abs-pred-abs)
        
   ;; IMPROVE ME: for all (C_1 -> C_2) in C ..., you know C_2 of result.
   (--> ((-- (C_1 -> C_2) C ...) V f)
        (begin ((demonic C_1) V #;(C_1 <= f ★ V f V) ★) (-- C_2))
        (side-condition (not (abstract-value? (term V))))
        apply-abs-func-concrete) 
   (--> ((-- (C_1 -> C_2) C ...) (-- C_0 ...) f)  
        #;(begin (C_1 <= f ★ (-- C_0 ...) f (-- C_0 ...))
                 (-- C_2))
        (-- C_2)
        apply-abs-func-abs)
   
   (--> ((-- int/c) V)
        (blame f Λ (-- int/c) λ (-- int/c))
        apply-abs-int)
   (--> (if (-- C C_0 ...) E_1 E_2)
        E_2
        if-abs-false)
   (--> (if (-- C C_0 ...) E_1 E_2)
        E_1
        if-abs-true)
   (--> (int/c <= f_1 f_2 V f_3 (-- int/c))
        (-- int/c)
        check-int-abs-int)
   (--> (int/c <= f_1 f_2 V f_3 (-- (pred SV) C ...))
        (-- int/c (pred SV) C ...)
        check-int-abs-pred-pass)
   (--> (int/c <= f_1 f_2 V f_3 (-- (pred SV) C ...))
        (blame f_1 f_3 V int/c (-- (pred SV) C ...))
        check-int-abs-pred-fail)
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- (pred SV) C ...))
        (-- (C_1 -> C_2) (pred SV) C ...)
        check-func-abs-pred-pass)
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- (pred SV) C ...))
        (blame f_1 f_3 V (C_1 -> C_2) (-- (pred SV) C ...))
        check-func-abs-pred-fail)
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- int/c C ...))
        (blame f_1 f_3 V (C_1 -> C_2) (-- int/c C ...))
        check-func-abs-int-fail)
   
   (--> (C <= f_1 f_2 V f_3 (-- C_0 ... C C_1 ...))
        (-- C_0 ... C C_1 ...)
        (side-condition (not (redex-match λc~ (C_a -> C_b) (term C))))
        smart*)
   
   ;; Possible overlapping
   (--> ((pred (f_a ^ f_b)) <= f_1 f_2 V f_3 (-- C_0 ... (pred (f_a ^ f_c)) C_1 ...))
        (-- C_0 ... (pred (f_a ^ f_b)) C_1 ...)
        (side-condition (not (eq? (term f_b) (term f_c))))
        smart*-pred-mod)
   
   ;; sugar
   #;
   (--> ((-- any/c) V f)
        (begin ((demonic any/c) V ★) (-- any/c)))
   
   (--> ((-- any/c C ...) V f)
        (begin ((demonic any/c) V ★) (-- any/c))
        (side-condition (not (abstract-value? (term V))))
        apply-abs-any-concrete)
   (--> ((-- any/c C ...) (-- C_0 ...) f)
        (-- any/c)
        apply-abs-any-abs)      
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- any/c))
        (blame f_1 f_3 V (C_1 -> C_2) (-- any/c)))   
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- any/c))
        (-- (C_1 -> C_2)))
   (--> (int/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (-- int/c C ...))
   (--> (int/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (blame f_1 f_3 V int/c (-- any/c C ...)))
   (--> (bool/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (-- bool/c C ...))
   (--> (bool/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (blame f_1 f_3 V bool/c (-- any/c C ...)))
   (--> (string/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (-- string/c C ...))   
   (--> (string/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (blame f_1 f_3 V string/c (-- any/c C ...)))))

(define (Δ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f ^ f)
        V
        (where (M_1 ... (module f C V) M_2 ...) ,Ms)
        Δ-self)
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 V f_1 V)
        (where (M_1 ... (module f_1 C V) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2))))
        Δ-other)))

(test--> (Δ (term [(module f any/c 0)]))
         (term (f ^ f))
         (term 0))
(test--> (Δ (term [(module f any/c 0)]))
         (term (f ^ g))
         (term (any/c <= f g 0 f 0)))

(define (Δ~ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f ^ f)
        V
        (where (M_1 ... (module f C V) M_2 ...) ,Ms)
        self-mod-ref)
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 V f_1 V)
        (where (M_1 ... (module f_1 C V) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2))))
        concrete-mod-ref)
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 (-- C) f_1 (-- C))
        #;(-- C)
        (where (M_1 ... (module f_1 C ☁) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2))))
        opaque-mod-ref)))

(test--> (context-closure (Δ~ (term [(module prime? any/c ☁)])) λc~ 𝓔)
         (term ((prime? ^ rsa)
                (--
                 (pred
                  (prime? ^ keygen)))
                Λ))         
         (term ((any/c <= prime? rsa (-- any/c) prime? (-- any/c))
                (--
                 (pred
                  (prime? ^ keygen)))
                 Λ)))

(test--> (Δ~ (term [(module prime? any/c ☁)]))
         (term (prime? ^ rsa))
         (term (any/c <= prime? rsa (-- any/c) prime? (-- any/c))))

(test--> (Δ~ (term [(module f any/c ☁)]))
         (term (f ^ g))
         (term (any/c <= f g (-- any/c) f (-- any/c))))

;; when we get blame, discard the context
(define error-propagate
  (reduction-relation 
   λc~ #:domain E
   (--> (in-hole 𝓔 (-- none/c)) (-- none/c)
        (side-condition (not (equal? (term hole) (term 𝓔)))))
   (--> (in-hole 𝓔 B) B
        (side-condition (not (equal? (term hole) (term 𝓔)))))))

(define (-->_vcΔ Ms)
  (union-reduction-relations error-propagate (context-closure (union-reduction-relations v c (Δ Ms)) λc~ 𝓔)))

(define (-->_vcc~Δ Ms)
  (union-reduction-relations error-propagate (context-closure (union-reduction-relations v c c~ (Δ~ Ms)) λc~ 𝓔)))

(define-syntax-rule (test-->>p p e ...)
  (test-->> (-->_vcc~Δ (all-but-last p)) (last p)
            e ...))

(test-->>p fit-example (term (-- string/c)))
(test-->>p fit-example-keygen-string
           (term (blame keygen prime? "Key" int/c "Key")))
(test-->>p fit-example-rsa-7
           (term (-- string/c))
           (term (blame keygen keygen (λ x 7) (pred (prime? ^ keygen)) 7)))

(test-->>p example-8 (term (blame h g #f (pred (λ x x)) #f)))
(test-->>p example-8-opaque 
           (term (-- any/c))
           (term (blame h g (-- any/c) (pred (λ x x)) (-- any/c)))
           #;(term (blame h g #f (pred (λ x x)) #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluation functions

(define (eval_vcΔ P)
  (apply-reduction-relation* (-->_vcΔ (all-but-last P))
                             (last P)))

(define (eval_vcc~Δ P)
  (apply-reduction-relation* (-->_vcc~Δ (all-but-last P))
                             (last P)))

(test-predicate (redex-match λc 
                  [(in-hole 𝓔 (blame h g #f (pred (λ x x)) #f))])
                (eval_vcΔ example-8))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trace and stepper

(define-syntax-rule (trace-it R P)
  (traces (R (all-but-last P))
          (last P)
          #:pred colorize))

(define (colorize x)
  (cond [(redex-match λc~ V x) "green"]
        [(redex-match λc~ (blame ★ f V_0 C V_1) x) "pink"]
        [(redex-match λc~ B x) "red"]
        [else #t]))

(define-syntax-rule (step-it R P)
  (stepper (R (all-but-last P))
           (last P)))

;(trace-it -->_vcc~Δ fit-example)
;(trace-it -->_vcc~Δ fit-example-rsa-7)
;(trace-it -->_vcc~Δ fit-example-keygen-string)
;(step-it -->_vcc~Δ fit-example)


#;
(traces (-->_vcΔ (all-but-last example-8))
        (last example-8))
#;
(traces (-->_vcc~Δ (all-but-last example-8-opaque))
        (last example-8-opaque))


