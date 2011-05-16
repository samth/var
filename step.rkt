#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "test.rkt" "annotate.rkt")
(provide (all-defined-out))

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
        (δ (@ o V ... ℓ))
        δ)   
   (--> (begin V E) E begin)
   (--> (let x V E)
        (subst x V E) let)))
  
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


(define -->_v (context-closure v λc~ 𝓔))

(test-->> -->_v (term (@ (λ x 0) 1 †)) (term (-- 0)))                
(test-->> -->_v (term (@ 0 1 †)) (term (blame † Λ (-- 0) λ (-- 0))))
(test-->> -->_v (term (if 0 1 2)) (term (-- 1)))
(test-->> -->_v (term (if #t 1 2)) (term (-- 1)))
(test-->> -->_v (term (if #f 1 2)) (term (-- 2)))
(test-->> -->_v (term (@ add1 0 †))  (term (-- 1)))
(test-->> -->_v (term (@ proc? #f †)) (term (-- #f)))
(test-->> -->_v (term (@ cons 1 2 †)) (term (-- (cons (-- 1) (-- 2)))))

(define c
  (reduction-relation
   λc~ #:domain E
   
   ;; BASE CONTRACTS
   
   (--> (FC <= ℓ_1 ℓ_2 V ℓ_3 (-- PV C ...)) 
        (remember-contract (-- PV C ...) FC)
        (where #t (flat-pass FC PV))
        chk-flat-pass)
   
   (--> (FC <= ℓ_1 ℓ_2 V ℓ_3 (-- PV C ...)) 
        (blame ℓ_1 ℓ_3 V FC (-- PV C ...))
        (where #f (flat-pass FC PV))
        chk-flat-fail)       
   
   ;; OR CONTRACTS
   
   (--> ((or/c FC FLAT) <= ℓ_1 ℓ_2 V_0 ℓ_3 (-- PV C ...))
        (remember-contract (-- PV C ...) FC)
        (where #t (flat-pass FC PV))
        or/c-fc-pass)
   (--> ((or/c FC FLAT) <= ℓ_1 ℓ_2 V_0 ℓ_3 (-- PV C ...))
        (FLAT <= ℓ_1 ℓ_2 V_0 ℓ_3 (-- PV C ...))
        (where #f (flat-pass FC PV))
        or/c-fc-fail)   
   (--> ((or/c none/c FLAT) <= ℓ_1 ℓ_2 V_0 ℓ_3 V)
        (blame ℓ_1 ℓ_3 V_0 none/c V))
   (--> ((or/c any/c FLAT) <= ℓ_1 ℓ_2 V_0 ℓ_3 V)
        (FLAT <= ℓ_1 ℓ_2 V_0 ℓ_3 V))
   (--> ((or/c (pred SV) FLAT) <= ℓ_1 ℓ_2 V_1 ℓ_3 V_2)
        (if (@ SV V_2 Λ) 
            (remember-contract V_2 (pred SV))
            (FLAT <= ℓ_1 ℓ_2 V_1 ℓ_3 V_2))
        chk-or/c-pred)
   (--> ((or/c (cons/c FLAT_0 FLAT_1) FLAT) <= ℓ_1 ℓ_2 V_0 ℓ_3 V)
        ;; FIXME
        (error "Not implemented"))
   (--> ((or/c (or/c FLAT_0 FLAT_1) FLAT_2) <= ℓ_1 ℓ_2 V_0 ℓ_3 V)
        ((or/c FLAT_0 (or/c FLAT_1 FLAT_2)) <= ℓ_1 ℓ_2 V_0 ℓ_3 V))
   (--> ((or/c (and/c FLAT_0 FLAT_1) FLAT_2) <= ℓ_1 ℓ_2 V_0 ℓ_3 V)
        ;; FIXME
        (error "Not implemented"))
   
   ;; AND CONTRACTS
   
   (--> ((and/c C_0 C_1) <= ℓ_1 ℓ_2 V_0 ℓ_3 V)
        (C_1 <= ℓ_1 ℓ_2 V_0 ℓ_3 
             (C_0 <= ℓ_1 ℓ_2 V_0 ℓ_3 V)))
   
   ;; PAIR CONTRACTS
   ;; FIXME: forgets what's known about the pair.
   
   (--> ((cons/c C_0 C_1) <= ℓ_1 ℓ_2 V ℓ_3 (-- (cons V_0 V_1) C ...))
        (@ cons 
           (C_0 <= ℓ_1 ℓ_2 V ℓ_3 V_0)
           (C_1 <= ℓ_1 ℓ_2 V ℓ_3 V_1)
           Λ)
        check-cons-pass)
   
   ;; PROCEDURE CONTRACTS   
      
   ;; definite procedures
   (--> ((C_1  -> C_2) <= ℓ_1 ℓ_2 V ℓ_3 W)
        (-- (λ y (C_2 <= ℓ_1 ℓ_2 V ℓ_3 
                      (@ W (C_1 <= ℓ_2 ℓ_1 y ℓ_3 y) Λ))))
        (fresh y)
        chk-fun-pass)
   
   ;; flat values
   (--> ((C_1 -> C_2) <= ℓ_1 ℓ_2 V ℓ_3 WFV)
        (blame ℓ_1 ℓ_3 V (C_1 -> C_2) WFV)
        chk-fun-fail-flat)
   
   ;; PREDICATE CONTRACTS
         
   (--> ((pred SV) <= ℓ_1 ℓ_2 V_1 ℓ_3 V_2)
        (if (@ SV V_2 Λ) 
            (remember-contract V_2 (pred SV))
            (blame ℓ_1 ℓ_3 V_1 (pred SV) V_2))
        ;; Only want smart to fire when this is true
        (where #f (contract-in (pred SV) V_2))
        chk-pred-c)
   
   ;; TRIVIAL CONTRACTS
   
   (--> (any/c <= ℓ_1 ℓ_2 V_1 ℓ_3 V_2) V_2 chk-any-pass)
   (--> (none/c <= ℓ_1 ℓ_2 V_1 ℓ_3 V_2) 
        (blame ℓ_1 ℓ_3 V_1 none/c V_2)
        chk-none-fail)))

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
         (term ((pred (λ x 0)) <= f g (-- 0) f (-- 5)))
         (term (if (@ (λ x 0) (-- 5) Λ)
                   (-- 5 (pred (λ x 0)))
                   (blame f f (-- 0) (pred (λ x 0)) (-- 5)))))
(test--> c
         (term ((and/c nat/c empty/c) <= f g (-- 0) f (-- #t)))
         (term (empty/c <= f g (-- 0) f
                        (nat/c <= f g (-- 0) f (-- #t)))))
               

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
   (--> (C <= ℓ_1 ℓ_2 V_0 ℓ_3 V)
        V        
        (side-condition (not (redex-match λc~ (C_a -> C_b) (term C))))
        (where #t (contract-in C V))
        smart*)
   
   ;; possible procedures
   (--> ((C_1  -> C_2) <= ℓ_1 ℓ_2 V ℓ_3 W?)
        (-- (λ y (C_2 <= ℓ_1 ℓ_2 V ℓ_3 
                      (@ (remember-contract W? (none/c -> any/c))
                         (C_1 <= ℓ_2 ℓ_1 y ℓ_3 y) Λ))))
        (fresh y)
        (side-condition (not (redex-match λc~ W (term W?))))
        (side-condition (not (redex-match λc~ WFV (term W?))))
        chk-fun-pass-maybe-proc)

   (--> ((C_1  -> C_2) <= ℓ_1 ℓ_2 V ℓ_3 W?)
        (blame ℓ_1 ℓ_3 V (C_1 -> C_2) W?)
        ;; definite procedures/non-procedures are handled in `v'
        (side-condition (not (redex-match λc~ W (term W?))))
        (side-condition (not (redex-match λc~ WFV (term W?))))
        chk-fun-fail-maybe-proc)

   
   ;; check flat contracts of abstract values   
   (--> (FC <= ℓ_1 ℓ_2 V ℓ_3 AV)
        (remember-contract AV FC)
        ;; avoid overlap with `smart*'
        (where #f (contract-in FC AV))
        ;; if AV is definitely not an FC, then there's no reason to pass
        (where #t (contract-not-in FC AV))
        chk-flat-abstract-pass)
   (--> (FC <= ℓ_1 ℓ_2 V ℓ_3 AV)
        (blame ℓ_1 ℓ_3 V FC AV)
        ;; avoid overlap with `smart*'
        (where #f (contract-in FC AV))
        chk-flat-abstract-fail)))

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

(test--> (∆ (term [(module f any/c 0)]))
         (term (f ^ f))
         (term (-- 0)))
(test--> (∆ (term [(module f any/c 0)]))
         (term (f ^ g))
         (term (any/c <= f g (-- 0) f (-- 0))))

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

(test--> (context-closure (Δ~ (term [(module prime? any/c ☁)])) λc~ 𝓔)
         (term (@ (prime? ^ rsa)
                  (--
                   (pred
                    (prime? ^ keygen)))
                  Λ))         
         (term (@ (any/c <= prime? rsa (-- any/c) prime? (-- any/c))
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
   ;; if we reduce to blame, we halt the program
   (--> (in-hole 𝓔 B) B
        (side-condition (not (equal? (term hole) (term 𝓔))))
        halt-blame)
   ;; abstract none/c values are impossible
   (--> (in-hole 𝓔 (-- any_0 ... none/c any_1 ...))
        (-- any_0 ... none/c any_1 ...)
        (side-condition (not (equal? (term hole) (term 𝓔))))
        halt-none/c)   
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

(test-->>p (term [(@ (-- (λ o (b ^ o))) (-- "") sN)])
           (term (b ^ o)))
(test-->>p (term [(@ (-- (λ o (@ 4 5 o))) (-- "") sN)])
           (term (blame o Λ (-- 4) λ (-- 4))))
(test-->>p (term (ann [(module n (and/c nat/c nat/c) 1) n]))
           (term (-- 1)))
(test-->>p (term (ann [(module n (and/c nat/c (pred (λ x (= x 7)))) 7) n]))
           (term (-- 7 (pred (λ x (@ = x 7 n))))))
(test-->>p (term (ann [(module n (and/c nat/c (pred (λ x (= x 8)))) 7) n]))
           (term (blame n n (-- 7) (pred (λ x (@ = x 8 n))) (-- 7))))
(test-->>p (term (ann [(module n (and/c nat/c (pred (λ x (= x 8)))) "7") n]))
           (term (blame n n (-- "7") nat/c (-- "7"))))
                
(test-->>p fit-example (term (-- string/c)))
(test-->>p fit-example-keygen-string
           (term (blame keygen prime? (-- "Key") nat/c (-- "Key"))))
(test-->>p fit-example-rsa-7
           (term (-- string/c))
           (term (blame keygen keygen (-- (λ x 7)) (pred (prime? ^ keygen)) (-- 7))))

(test-->>p example-8 (term (blame h g (-- #f) (pred (λ x x)) (-- #f))))
(test-->>p example-8-opaque 
           (term (-- any/c))
           (term (blame h g (-- any/c) (pred (λ x x)) (-- any/c))))

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
           (term (-- (cons (-- 1) (-- 2)))))

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
                                    #f))))))

(test-->>p (term (ann [(module p
                         (and/c (cons/c nat/c nat/c)
                                (pred (λ x (= (first x) (rest x)))))
                         (cons (-- 1) (-- 1)))
                       p]))
           (term (-- (cons (-- 1) (-- 1))
                     (pred (λ x (@ = (@ first x p) (@ rest x p) p))))))

;; Swap of and/c arguments above
;; FIXME: fails to remember predicate on pair
(test-->>p (term (ann [(module p
                         (and/c (pred (λ x (= (first x) (rest x))))
                                (cons/c nat/c nat/c))                                
                         (cons (-- 1) (-- 1)))
                       p]))
           (term (-- (cons (-- 1) (-- 1))
                     (pred (λ x (@ = (@ first x p) (@ rest x p) p))))))

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

;; Run a concrete program in concrete and abstract semantics, get same thing.
(redex-check λc-user (M ... E)
             (equal? (apply-reduction-relation (-->_vcΔ (term (M ...))) (term E))
                     (apply-reduction-relation (-->_vcc~Δ (term (M ...))) (term E))))
