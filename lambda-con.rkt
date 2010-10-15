#lang racket
(require redex)

(define-language λc-user
  (P (M ... E))
  (M (module f C V))
  (L (λ x E))
  (W L)
  (V n W)
  (E V x (f ^ f) (E E f) (if0 E E E))
  (C int any/c (C -> C) (pred L))
  (x variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned †)
  (n number)
  (Ε hole (Ε E f) (V Ε f) (if0 Ε E E)))
  
(define-extended-language λc λc-user
  (W .... ((C --> C) <= f f V f W))
  (B (blame f f V C V))
  (E .... (C <= f f V f E) B)
  (C .... (C --> C) λ)
  (f .... Λ)
  (Ε .... (C <= f f V f Ε)))

(define-extended-language λc~ λc
  (V .... (-- C))
  (B .... (blame f? g? V1? C? V2?))
  (M .... (module f C ☁))
  (W .... (-- (C -> C)) (-- (pred L))))

(define example-8
  (term [(module f (any/c -> (any/c -> any/c)) (λ x x))
         (module g ((pred (λ x x)) -> int) (λ x 0))
         (module h any/c (λ z (((f ^ h) (g ^ h) h) 8 h)))
         ((h ^ †) 0 †)]))

(test-predicate (redex-match λc-user P) example-8)
(test-predicate (redex-match λc P) example-8)
(test-predicate (redex-match λc~ P) example-8)

(define-metafunction λc~ subst : x any any -> any  
  ;; 1. x bound, so don't continue in λ body  
  [(subst x any_1 (λ x any_2)) 
   (λ x any_2)] 
  ;; 2. general purpose capture avoiding case  
  [(subst x_1 any_1 (λ x_2 any_2)) 
   (λ x_new
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

(define v
  (reduction-relation
   λc~ #:domain E
   (--> ((λ x E) V f) (subst x V E) β)
   (--> (n V f) (blame f Λ n λ n) wrong)
   (--> (if0 0 E_1 E_2) E_1 if0-0)
   (--> (if0 V E_1 E_2) E_2 
        (side-condition (not (eqv? 0 (term V)))) 
        if0-!0)))
   
(test--> v (term ((λ x 0) 1 †)) (term 0))
(test--> v (term (0 1 †)) (term (blame † Λ 0 λ 0)))
(test--> v (term (if0 0 1 2)) (term 1))
(test--> v (term (if0 5 1 2)) (term 2))

(define (Δ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f ^ f)
        V
        (where (M_1 ... (module f C V) M_2 ...) ,Ms))
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 V f_1 V)
        (where (M_1 ... (module f_1 C V) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2)))))))

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
        (where (M_1 ... (module f C V) M_2 ...) ,Ms))
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 V f_1 V)
        (where (M_1 ... (module f_1 C V) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2)))))
   (--> (f_1 ^ f_2)
        (-- C)
        (where (M_1 ... (module f_1 C ☁) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2)))))))

(test--> (Δ~ (term [(module f any/c ☁)]))
         (term (f ^ g))
         (term (-- any/c)))

(define c
  (reduction-relation
   λc~ #:domain E
   (--> (((C_1 --> C_2) <= f_1 f_2 V_1 f_3 W) V_2 f_4)
        (C_2 <= f_1 f_2 V_1 f_3 (W (C_1 <= f_2 f_1 V_1 f_3 V_2) f_4))
        split)   
   (--> (int <= f_1 f_2 V f_3 n) n chk-int-pass)
   (--> (int <= f_1 f_2 V f_3 W) 
        (blame f_1 f_3 V int W)
        chk-int-fail)
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 W)
        ((C_1 --> C_2) <= f_1 f_2 V f_3 W)
        chk-fun-pass)
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 n)
        (blame f_1 f_3 V (C_1 -> C_2) n)
        chk-fun-fail)
   (--> ((pred L) <= f_1 f_2 V_1 f_3 V_2)
        (if0 (L V_2 Λ) V_2 (blame f_1 f_3 V_1 (pred L) V_2))
        chk-pred)
   
   ;; sugar
   (--> (any/c <= f_1 f_2 V_1 f_3 V_2) V_2 any-pass)))

;; when we get blame, discard the context
(define error-propagate
  (reduction-relation 
   λc~ #:domain E
   (--> (in-hole Ε B) B
        (side-condition (not (equal? (term hole) (term Ε)))))))


(test--> c 
         (term (((any/c --> any/c) <= f g 7 f (λ x 5)) 8 †))
         (term (any/c <= f g 7 f ((λ x 5) (any/c <= g f 7 f 8) †))))
(test--> c (term (int <= f g 0 f 5)) (term 5))
(test--> c 
         (term (int <= f g 0 f (λ x x))) 
         (term (blame f f 0 int (λ x x))))
(test--> c
         (term ((any/c  -> any/c) <= f g 0 f (λ x x)))
         (term ((any/c --> any/c) <= f g 0 f (λ x x))))
(test--> c 
         (term ((any/c  -> any/c) <= f g 0 f 5))
         (term (blame f f 0 (any/c -> any/c) 5)))
(test--> c
         (term ((pred (λ x 0)) <= f g 0 f 5))
         (term (if0 ((λ x 0) 5 Λ)
                    5
                    (blame f f 0 (pred (λ x 0)) 5))))

(define c~
  (reduction-relation
   λc~ #:domain E
   (--> ((-- (pred L)) V f)
        (-- any/c))
   (--> ((-- (pred L)) V f)
        (blame f? g? V1? C? V2?))
   (--> ((-- (C_1 -> C_2)) V f)
        (-- C_2))
   (--> ((-- (C_1 -> C_2)) V f)
        (blame f? g? V1? C? V2?))
   (--> ((-- int) V)
        (blame f Λ (-- int) λ (-- int)))
   (--> (if0 (-- C) E_1 E_2)
        E_2)
   (--> (if0 (-- int) E_1 E_2)
        E_1)
   (--> (if0 (-- (pred L)) E_1 E_2)
        E_1)
   (--> (int <= f_1 f_2 V f_3 (-- int))
        (-- int))
   (--> (int <= f_1 f_2 V f_3 (-- (pred L)))
        (-- int))   
   (--> (int <= f_1 f_2 V f_3 (-- (pred L)))
        (blame f_1 f_3 V int (-- (pred L))))
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- (pred L)))
        (-- (C_1 -> C_2)))
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- (pred L)))
        (blame f_1 f_3 V (C_1 -> C_2) (-- (pred L))))
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- int))
        (blame f_1 f_3 V (C_1 -> C_2) (-- int)))
   
   ;; sugar
   (--> ((-- any/c) V f)
        (-- any/c))
   (--> ((-- any/c) V f)
        (blame f? g? V1? C? V2?))
   (--> (if0 (-- any/c) E_1 E_2)
        E_1)   
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- any/c))
        (blame f_1 f_3 V (C_1 -> C_2) (-- any/c)))   
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- any/c))
        (-- (C_1 -> C_2)))
   (--> (int <= f_1 f_2 V f_3 (-- any/c))
        (-- int))
   (--> (int <= f_1 f_2 V f_3 (-- any/c))
        (blame f_1 f_3 V int (-- any/c)))))
   
   
(define example-8-opaque
  (term [(module f (any/c -> (any/c -> any/c)) ☁)
         (module g ((pred (λ x x)) -> int) ☁)
         (module h any/c (λ z (((f ^ h) (g ^ h) h) 8 h)))
         ((h ^ †) 0 †)]))


(test-predicate (redex-match λc~ P) example-8-opaque)

(define (all-but-last ls)
  (cond [(empty? (rest ls)) empty]
        [else (cons (first ls)
                    (all-but-last (rest ls)))]))
  
(define (-->_vcΔ Ms)
  (union-reduction-relations error-propagate (context-closure (union-reduction-relations v c (Δ Ms)) λc~ Ε)))

(define (-->_vcc~Δ Ms)
  (union-reduction-relations error-propagate (context-closure (union-reduction-relations v c c~ (Δ~ Ms)) λc~ Ε)))


(define (eval_vcΔ P)
  (apply-reduction-relation* (-->_vcΔ (all-but-last P))
                             (last P)))

(define (eval_vcc~Δ P)
  (apply-reduction-relation* (-->_vcc~Δ (all-but-last P))
                             (last P)))
#;
(test-predicate (redex-match λc 
                  [(in-hole Ε (blame h g (λ x 0) (pred (λ x x)) 8))])
                (eval_vcΔ example-8))
#;
(traces (-->_vcΔ (all-but-last example-8))
        (last example-8))
#;
(traces (-->_vcc~Δ (all-but-last example-8-opaque))
        (last example-8-opaque))
