#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "name.rkt" 
         "examples.rkt" "annotate.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test step)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relations

(define v
  (reduction-relation
   λc~ #:domain E
   (--> PV (-- PV) wrap)
   (--> (@ (-- (λ x E) C ...) V ℓ) 
        (subst x V E) 
        β)
   (--> (@ (-- (λ x_0 x_1 E) C ...) V ℓ) 
        (subst x_0 (-- (λ x_0 x_1 E) C ...) (subst x_1 V E)) 
        β-rec)   
   (--> (@ WFV V ℓ) (blame ℓ Λ WFV λ WFV) wrong)
   
   (--> (if V E_1 E_2) E_1
        (where (-- PV C ...) V)
        (side-condition (term PV))
        if-t)
   (--> (if V E_1 E_2) E_2 
        (where (-- PV C ...) V)
        (side-condition (not (term PV)))
        if-f)   
   (--> (@ o V ... ℓ)
        V-or-B
        (where (V-or-B_1 ... V-or-B V-or-B_2 ...)
               (δ (@ o V ... ℓ)))
        δ)   
   (--> (begin V E) E begin)
   (--> (let x V E)
        (subst x V E) let)))

(define -->_v (context-closure v λc~ 𝓔))
(test
 (test--> v (term (@ (-- (λ x 0)) (-- 1) †)) (term 0))
 (test--> v 
          (term (@ (-- (λ f x (@ f x †))) (-- 0) †))
          (term (@ (-- (λ f x (@ f x †))) (-- 0) †)))                 
 (test--> v (term (@ (-- 0) (-- 1) †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test--> v (term (if (-- 0) 1 2)) (term 1))
 (test--> v (term (if (-- #t) 1 2)) (term 1))
 (test--> v (term (if (-- #f) 1 2)) (term 2))
 (test--> v (term (@ add1 (-- 0) †)) (term (-- 1)))
 (test--> v (term (@ proc? (-- #f) †)) (term (-- #f)))
 (test--> v (term (@ proc? (-- (λ x x)) †)) (term (-- #t)))
 (test--> v (term (@ proc? (-- (λ f x x)) †)) (term (-- #t)))
 (test--> v (term (@ proc? (-- (any/c -> any/c)) †)) (term (-- #t)))
 (test--> v (term (@ cons (-- 1) (-- 2) †)) (term (-- (cons (-- 1) (-- 2)))))
 
 (test-->> -->_v (term (@ (λ x 0) 1 †)) (term (-- 0)))                
 (test-->> -->_v (term (@ 0 1 †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test-->> -->_v (term (if 0 1 2)) (term (-- 1)))
 (test-->> -->_v (term (if #t 1 2)) (term (-- 1)))
 (test-->> -->_v (term (if #f 1 2)) (term (-- 2)))
 (test-->> -->_v (term (@ add1 0 †))  (term (-- 1)))
 (test-->> -->_v (term (@ proc? #f †)) (term (-- #f)))
 (test-->> -->_v (term (@ cons 1 2 †)) (term (-- (cons (-- 1) (-- 2))))))

(define flat? (redex-match λc~ FLAT))

(define c
  (reduction-relation
   λc~ #:domain E
   
   ;; FLAT CONTRACTS
   
   (--> (FLAT <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (flat-check FLAT V
                    (remember-contract V FLAT)
                    ,(λ (f v) (term (blame ℓ_1 ℓ_3 V-or-AE ,f ,v))))
        flat-check)
   
   ;; HIGHER-ORDER CONTRACTS
   
   (--> ((or/c FLAT HOC) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (flat-check FLAT V
                    (remember-contract V FLAT)
                    ,(λ (f v) (term (HOC <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)))))
   (--> ((and/c C_0 C_1) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (C_1 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 
             (C_0 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V))
        (where HOC (and/c C_0 C_1)))
   
   ;; PAIR CONTRACTS
   ;; FIXME: forgets what's known about the pair.
   
   (--> ((cons/c C_0 C_1) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 (-- (cons V_0 V_1) C ...))
        (@ cons 
           (C_0 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V_0)
           (C_1 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V_1)
           Λ)
        (where HOC (cons/c C_0 C_1))
        check-cons-pass)
   
   ;; PROCEDURE CONTRACTS   
      
   ;; definite procedures
   (--> ((C_1  -> C_2) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 W)
        (-- (λ y (C_2 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 
                      (@ W (C_1 <= ℓ_2 ℓ_1 y ℓ_3 y) Λ))))
        (fresh y)
        chk-fun-pass)
   
   ;; flat values
   (--> ((C_1 -> C_2) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 WFV)
        (blame ℓ_1 ℓ_3 V-or-AE (C_1 -> C_2) WFV)
        chk-fun-fail-flat)))

(test
 (test--> c (term (nat/c <= f g (-- 0) f (-- 5))) (term (-- 5)))
 (test--> c 
          (term (nat/c <= f g (-- 0) f (-- (λ x x))))
          (term (blame f f (-- 0) nat/c (-- (λ x x)))))
 (test--> c 
          (term (nat/c <= f g (-- 0) f (-- #t))) 
          (term (blame f f (-- 0) nat/c (-- #t))))
 (test--> c
          (term ((any/c  -> any/c) <= f g (-- 0) f (-- (λ x x))))
          (term (-- (λ y (any/c <= f g (-- 0) f 
                                (@ (-- (λ x x)) (any/c <= g f y f y) Λ))))))
 (test--> c 
          (term ((any/c  -> any/c) <= f g (-- 0) f (-- 5)))
          (term (blame f f (-- 0) (any/c -> any/c) (-- 5))))
 (test--> c
          (term ((pred (λ x 0) ℓ) <= f g (-- 0) f (-- 5)))
          (term (if (@ (λ x 0) (-- 5) ℓ)
                    (-- 5 (pred (λ x 0) ℓ))
                    (blame f f (-- 0) (pred (λ x 0) ℓ) (-- 5)))))
 (test--> c
          (term ((and/c nat/c empty/c) <= f g (-- 0) f (-- #t)))
          (term (blame f f (-- 0) nat/c (-- #t)))))
               

(define c~
  (reduction-relation
   λc~ #:domain E
   
   ;; APPLYING ABSTRACT VALUES   
   
   ;; applying abstract values to concrete values
   (--> (@ AV V ℓ)
        ;; do bad things to the concrete value
        (begin (@ (demonic C_demon) V ★)
               ;; abstract value constranated by all possible domains
               (remember-contract (-- any/c) C_0 ...))
        (where (-- C ...) AV)
        (where C_demon (most-specific-domain C ...))
        (where (C_0 ...) (range-contracts (C ...)))
        ;; abstract values as arguments go in the next case
        (side-condition (not (abstract-value? (term V))))
        ;; if definitely flat, case is handled by `wrong' from `v'
        (side-condition (not (redex-match λc~ WFV (term AV))))
        apply-abs-concrete) 
   (--> (@ AV AV_0 ℓ)
        ;; don't care what bad things happen to abstract values, so we
        ;; don't simulate them
        (remember-contract (-- any/c) C_0 ...)
        (where (-- C ...) AV)
        (where (C_0 ...) (range-contracts (C ...)))
        ;; if definitely flat, case is handled by `wrong' from `v'
        (side-condition (not (redex-match λc~ WFV (term AV))))
        apply-abs-abs)
   
   ;; applying abstract value that might be flat can fail
   (--> (@ W? V ℓ)
        (blame ℓ Λ W? λ W?)
        ;; if it's not definitely a procedure, it might be flat        
        (side-condition (not (redex-match λc~ W (term W?))))
        apply-abs-fail)
   ;; applying definitely flat values (those not in W?) is handled by
   ;; `wrong' from `v'
   
   
   ;; CONDITIONALS ON ABSTRACT VALUES
   
   (--> (if AV E_1 E_2)
        E_2
        ;; if AV is an int, string, or procedure, then it can't be #f
        (side-condition (not (or (redex-match λc~ anat (term AV))
                                 (redex-match λc~ astring (term AV))
                                 (redex-match λc~ W (term AV)))))
        if-abs-false)
   (--> (if AV E_1 E_2)
        E_1
        if-abs-true)
   
   ;; CONTRACT CHECKING OF ABSTRACT VALUES
   
   ;; Predicate contracts are handled by concrete transition.
   
   ;; skip first-order checks that we know this value to have already
   ;; passed higher-order checks impose obligations on people we
   ;; interact with, so they must be kept around also, higher-order
   ;; checks could fail later even if they passed earlier

   ;; FIXME: if we add state, then we can't remember stateful predicates or 
   ;; predicates on stateful values
   
   ;; possible procedures
   (--> ((C_1  -> C_2) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 W?)
        (-- (λ y (C_2 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 
                      (@ (remember-contract W? (,none/c -> any/c))
                         (C_1 <= ℓ_2 ℓ_1 y ℓ_3 y) Λ))))
        (fresh y)
        (side-condition (not (redex-match λc~ W (term W?))))
        (side-condition (not (redex-match λc~ WFV (term W?))))
        chk-fun-pass-maybe-proc)

   (--> ((C_1  -> C_2) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 W?)
        (blame ℓ_1 ℓ_3 V-or-AE (C_1 -> C_2) W?)
        ;; definite procedures/non-procedures are handled in `v'
        (side-condition (not (redex-match λc~ W (term W?))))
        (side-condition (not (redex-match λc~ WFV (term W?))))
        chk-fun-fail-maybe-proc)
   
   ;; SPLITTING OR/C and REC/C ABSTRACT VALUES
   ;; Some introduced values are infeasible, which is still sound.
   (--> (-- C_0 ... (or/c C_1 ... C_2 C_3 ...) C ...)
        (remember-contract (-- any/c C_0 ... C ...) C_2)
        (side-condition (term (valid? C_2)))
        abs-or/c-split)
   
   (--> (-- C_0 ... (rec/c x C_1) C ...)
        (remember-contract (-- any/c C_0 ... C ...)  (unroll (rec/c x C_1)))
        (side-condition (term (valid? (rec/c x C_1))))
        abs-rec/c-unroll)))
   
   
  
(define (∆ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f ^ f)
        (-- PV)
        (where (M_1 ... (module f C PV) M_2 ...) ,Ms)
        Δ-self)
   (--> (f ^ ℓ)
        (C <= f ℓ (-- PV) f (-- PV))
        (where (M_1 ... (module f C PV) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f) (term ℓ))))
        Δ-other)))

(test
 (test--> (∆ (term [(module f any/c 0)]))
          (term (f ^ f))
          (term (-- 0)))
 (test--> (∆ (term [(module f any/c 0)]))
          (term (f ^ g))
          (term (any/c <= f g (-- 0) f (-- 0)))))

(define (Δ~ Ms)
  (union-reduction-relations
   (∆ Ms)
   (reduction-relation
    λc~ #:domain E
    (--> (f ^ ℓ)
         (C <= f ℓ (-- C) f (-- C))
         (where (M_1 ... (module f C ☁) M_2 ...) ,Ms)
         (side-condition (not (eq? (term f) (term ℓ))))
         ∆-opaque))))

(test
 (test--> (context-closure (Δ~ (term [(module prime? any/c ☁)])) λc~ 𝓔)
          (term (@ (prime? ^ rsa)
                   (-- (pred (prime? ^ keygen) keygen)) Λ))         
          (term (@ (any/c <= prime? rsa (-- any/c) prime? (-- any/c))
                   (-- (pred (prime? ^ keygen) keygen)) Λ)))
 
 (test--> (Δ~ (term [(module prime? any/c ☁)]))
          (term (prime? ^ rsa))
          (term (any/c <= prime? rsa (-- any/c) prime? (-- any/c))))
 
 (test--> (Δ~ (term [(module f any/c ☁)]))
          (term (f ^ g))
          (term (any/c <= f g (-- any/c) f (-- any/c)))))

;; when we get blame, discard the context
(define error-propagate
  (reduction-relation 
   λc~ #:domain E
   ;; if we reduce to blame, we halt the program
   (--> (in-hole 𝓔 B) B
        (side-condition (not (equal? (term hole) (term 𝓔))))
        halt-blame)
     
   ;; normalize abstract values at the end to make testing easier
   (--> V V_norm
        (where V_norm (normalize V))
        (side-condition (not (equal? (term V) (term V_norm))))
        normalize-abstract)))

(define (-->_vcΔ Ms)
  (union-reduction-relations error-propagate 
                             (context-closure (union-reduction-relations v c (∆ Ms)) λc~ 𝓔)))

(define (-->_vcc~Δ Ms)
  (union-reduction-relations error-propagate 
                             (context-closure (union-reduction-relations v c c~ (Δ~ Ms)) λc~ 𝓔)))

;; A sometimes useful utility
#;
(define (step p)
  (match (apply-reduction-relation (-->_vcc~Δ (all-but-last p))
                                   (last p))
    [(list e) (append (all-but-last p) (list e))]))

(define-syntax-rule (test-->>p p e ...)
  (test-->> (-->_vcc~Δ (all-but-last p))
            #:equiv (λ (e0 e1) (term (≡α ,e0 ,e1)))
            (last p)
            e ...))

(define none/c (term (pred (λ x #f) Λ)))

(test
 
 (test-->>p (term [(string/c <= |†| rsa (-- "Plain") rsa (-- "Plain"))])
             (term (-- "Plain")))
 
 (test-->>p (term [(@ (-- (λ o (b ^ o))) (-- "") sN)])
            (term (b ^ o)))
 (test-->>p (term [(@ (-- (λ o (@ 4 5 o))) (-- "") sN)])
            (term (blame o Λ (-- 4) λ (-- 4))))
 (test-->>p (term (ann [(module n (and/c nat/c nat/c) 1) n]))
            (term (-- 1)))
 (test-->>p (term (ann [(module n (and/c nat/c (pred (λ x (= x 7)))) 7) n]))
            (term (-- 7 (pred (λ x (@ = x 7 n)) n))))
 (test-->>p (term (ann [(module n (and/c nat/c (pred (λ x (= x 8)))) 7) n]))
            (term (blame n n (-- 7) (pred (λ x (@ = x 8 n)) n) (-- 7))))
 (test-->>p (term (ann [(module n (and/c nat/c (pred (λ x (= x 8)))) "7") n]))
            (term (blame n n (-- "7") nat/c (-- "7"))))
 
 (test-->>p fit-example (term (-- string/c)))
 (test-->>p fit-example-keygen-string
            (term (blame keygen prime? (-- "Key") nat/c (-- "Key"))))
 (test-->>p fit-example-rsa-7
            (term (-- string/c))
            (term (blame keygen keygen (-- (λ x 7)) (pred (prime? ^ keygen) keygen) (-- 7))))
 
 (test-->>p example-8 (term (blame h g (-- #f) (pred (λ x x) g) (-- #f))))
 (test-->>p example-8-opaque 
            (term (-- any/c))
            (term (blame h g (-- any/c) (pred (λ x x) g) (-- any/c))))
 
 (test-->>p list-id-example (term (-- (cons (-- 1) 
                                            (-- (cons (-- 2) 
                                                      (-- (cons (-- 3) (-- empty)))))))))
 
 (test-->>p (term (ann ,list-rev-example-raw))
            (term (-- (cons (-- 3)
                            (-- (cons (-- 2)
                                      (-- (cons (-- 1)
                                                (-- empty)))))))))
 
 ;; Not sure about the remembered contracts in these examples.
 (test-->>p (term (ann [(module n nat/c 5) n]))
            (term (-- 5)))
 (test-->>p (term (ann [(module p
                          (cons/c nat/c nat/c)
                          (cons (-- 1) (-- 2)))
                        p]))
            (term (-- (cons (-- 1) (-- 2)) 
                      (cons/c nat/c nat/c))))
 
 (test-->>p (term (ann [(module p
                          (pred (λ x (if (cons? x)
                                         (= (first x)
                                            (rest x))
                                         #f)))
                          (cons (-- 1) (-- 1)))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (pred (λ x (if (@ cons? x p)
                                     (@ = 
                                        (@ first x p)
                                        (@ rest x p)
                                        p)
                                     #f))
                            p))))
 
 (test-->>p (term (ann [(module p
                          (and/c (cons/c nat/c nat/c)
                                 (pred (λ x (= (first x) (rest x)))))
                          (cons (-- 1) (-- 1)))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (cons/c nat/c nat/c) 
                      (pred (λ x (@ = (@ first x p) (@ rest x p) p)) p))))
 
 ;; Swap of and/c arguments above
 (test-->>p (term (ann [(module p
                          (and/c (pred (λ x (= (first x) (rest x))))
                                 (cons/c nat/c nat/c))                                
                          (cons (-- 1) (-- 1)))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (pred (λ x (@ = (@ first x p) (@ rest x p) p)) p)
                      (cons/c nat/c nat/c))))
 
 (test-->>p (term (ann [(module p
                          (cons/c nat/c nat/c)
                          (cons (-- 1) (-- 2)))
                        (first p)]))
            (term (-- 1)))
 (test-->>p (term (ann [(module p
                          (cons/c nat/c nat/c)
                          (cons (-- "hi") (-- 2)))
                        (first p)]))
            (term (blame p p (-- (cons (-- "hi") (-- 2))) nat/c (-- "hi"))))
 
 (test-->>p (term (ann [(module p
                          (cons/c (any/c -> nat/c) any/c)
                          (cons (-- (λ x "hi"))
                                (-- 7)))
                        ((first p) 7)]))
            (term (blame p p (-- (cons (-- (λ x "hi"))
                                       (-- 7)))
                         nat/c
                         (-- "hi"))))
 
 #|
 (test-->>p (term (ann [(module n (or/c  nat/c) 5) n]))
            (term (-- 5  (or/c ,none/c nat/c))))
 (test-->>p (term (ann [(module n (or/c nat/c ,none/c-raw) 5) n]))
            (term (-- 5)))
 (test-->>p (term (ann [(module n (or/c nat/c (,none/c -> ,none/c)) 5) n]))
            (term (-- 5)))
 (test-->>p (term (ann [(module f (or/c nat/c (,none/c -> ,none/c)) (λ x x)) f]))
            (term (-- (λ y (,none/c <= f † (-- (λ x x)) f 
                                   (@ (-- (λ x x)) 
                                      (,none/c <= † f y f y) Λ))))))
|#
 
 (test-->>p (term [(module mt (pred empty? mt) empty) (mt ^ †)])
            (term (-- empty (pred empty? mt))))
 
 (test-->>p list-id-example-contract
            (term (-- (cons (-- 1)
                            (-- (cons (-- 2)
                                      (-- (cons (-- 3)
                                                (-- empty))))))
                      ,list-of-nat/c)))
 
 ;; Run a concrete program in concrete and abstract semantics, get same thing.
 (redex-check λc-user (M ... E)
              (equal? (apply-reduction-relation (-->_vcΔ (term (M ...))) (term E))
                      (apply-reduction-relation (-->_vcc~Δ (term (M ...))) (term E)))))
