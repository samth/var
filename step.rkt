#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "flat-check.rkt" "meta.rkt" "subst.rkt" 
         "examples.rkt" "annotate.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test step)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relations

(define v
  (reduction-relation
   λc~ #:domain E
   (--> PV (-- PV) wrap)
   (--> (@ (-- (λ (x ..._1) E) C ...) V ..._1 ℓ)
        (subst/β ((x V) ...) E)
        β)
   (--> (@ (-- (λ x_0 (x_1 ..._1) E) C ...) V ..._1 ℓ)
        (subst/β ((x_0 (-- (λ x_0 (x_1 ...) E) C ...)) (x_1 V) ...) E)
        β-rec)
   (--> (@ V U ... ℓ)
        (blame ℓ  Λ V λ V)
        (side-condition (term (∈ #t (δ (@ proc? V ★)))))
        (side-condition (not (equal? (length (term (U ...)))
                                     (term (arity V)))))
        wrong-arity)
   (--> (@ V U ... ℓ)
        (blame ℓ Λ V λ V)
        (side-condition (term (∈ #f (δ (@ proc? V ★)))))
        wrong-not-proc)
   (--> (if V E_1 E_2) E_1
        (side-condition (term (∈ #f (δ (@ false? V ★)))))
        if-t)
   (--> (if V E_1 E_2) E_2
        (side-condition (term (∈ #t (δ (@ false? V ★)))))
        if-f)   
   (--> (@ o V ... ℓ)
        V-or-B
        (where (V-or-B_1 ... V-or-B V-or-B_2 ...)
               (δ (@ o V ... ℓ)))
        δ)   
   (--> (begin V E) E begin)
   (--> (let x V E)
        (subst/β ((x V)) E) let)))

(define -->_v (context-closure v λc~ 𝓔))

(test
 (test--> v (term (@ (-- (λ (x) 0)) (-- 1) †)) (term 0))
 (test--> v 
          (term (@ (-- (λ f (x) (@ f x †))) (-- 0) †))
          (term (@ (-- (λ f (x) (@ f x †))) (-- 0) †)))                 
 (test--> v (term (@ (-- 0) (-- 1) †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test--> v (term (if (-- 0) 1 2)) (term 1))
 (test--> v (term (if (-- #t) 1 2)) (term 1))
 (test--> v (term (if (-- #f) 1 2)) (term 2))
 (test--> v (term (@ add1 (-- 0) †)) (term (-- 1)))
 (test--> v (term (@ proc? (-- #f) †)) (term (-- #f)))
 (test--> v (term (@ proc? (-- (λ (x) x)) †)) (term (-- #t)))
 (test--> v (term (@ proc? (-- (λ f (x) x)) †)) (term (-- #t)))
 (test--> v (term (@ proc? (-- ((any/c) -> (any/c))) †)) (term (-- #t)))
 (test--> v (term (@ cons (-- 1) (-- 2) †)) (term (-- (cons (-- 1) (-- 2)))))
 
 (test-->> -->_v (term (@ (λ (x) 0) 1 †)) (term (-- 0)))                
 (test-->> -->_v (term (@ 0 1 †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test-->> -->_v (term (if 0 1 2)) (term (-- 1)))
 (test-->> -->_v (term (if #t 1 2)) (term (-- 1)))
 (test-->> -->_v (term (if #f 1 2)) (term (-- 2)))
 (test-->> -->_v (term (@ add1 0 †))  (term (-- 1)))
 (test-->> -->_v (term (@ proc? #f †)) (term (-- #f)))
 (test-->> -->_v (term (@ cons 1 2 †)) (term (-- (cons (-- 1) (-- 2))))))

(define flat? (redex-match λc~ FLAT))

;; Note: contract checking not strictly faithful to Racket, which checks the 
;; first-order portions of each first if they exist.  Racket also reports
;; most specific flat contract that fails (in or/c, and/c, cons/c), while we
;; just report the whole flat contract.
(define c
  (reduction-relation
   λc~ #:domain E
   
   ;; FLAT CONTRACTS   
   (--> (FLAT <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (if (@ (flat-check FLAT V) V Λ)
            (remember-contract V FLAT)
            (blame ℓ_1 ℓ_3 V-or-AE FLAT V))        
        flat-check)
   
   ;; HIGHER-ORDER CONTRACTS   
   (--> ((or/c FLAT HOC) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (if (@ (flat-check FLAT V) V Λ)
            (remember-contract V FLAT)
            (HOC <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V))
        or/c-hoc)
   
   (--> ((and/c C_0 C_1) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)        
        (C_1 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 
             (C_0 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V))
        (where HOC (and/c C_0 C_1))
        and/c-hoc)
   
   (--> ((rec/c x C) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        ((unroll HOC) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (where HOC (rec/c x C))
        unroll-HOC)
   
   ;; PAIR CONTRACTS
   ;; FIXME: forgets what's known about the pair.   
   (--> ((cons/c C_0 C_1) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (@ cons 
           (C_0 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 (@ first (remember-contract V (pred cons? Λ)) Λ))
           (C_1 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 (@ rest (remember-contract V (pred cons? Λ)) Λ))
           Λ)
        (where HOC (cons/c C_0 C_1))
        (where #t (∈ #t (δ (@ cons? V Λ))))
        check-cons-pass)
   
   (--> ((cons/c C_0 C_1) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (blame ℓ_1 ℓ_3 V-or-AE HOC V)
        (where HOC (cons/c C_0 C_1))
        (where #t (∈ #f (δ (@ cons? V Λ))))
        check-cons-fail)
   
   ;; PROCEDURE CONTRACTS      
   (--> (@ ((C_0 ..._1 --> (λ (x ..._1) C_1)) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V) V_1 ..._1 ℓ)        
        ((subst/C ((x (C_0 <= ℓ_2 ℓ_3 V_1 ℓ_2 V_1)) ...) C_1)
         <= ℓ_1 ℓ_2 V-or-AE ℓ_3 
         (@ (remember-contract V (C_arity ... -> (any/c))) (C_0 <= ℓ_2 ℓ_1 V_1 ℓ_3 V_1) ... Λ))
        (where (C_arity ...) ,(map (λ _ (term (any/c))) (term (C_0 ...))))
        blessed-β-dep)

   (--> (@ ((C_0 ..._1 --> C_1) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V) V_1 ..._1 ℓ)        
        (C_1 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 
             (@ (remember-contract V (C_arity ... -> (any/c))) (C_0 <= ℓ_2 ℓ_1 V_1 ℓ_3 V_1) ... Λ))
        (where (C_arity ...) ,(map (λ _ (term (any/c))) (term (C_0 ...))))
        blessed-β)
   
   ;; BLESSING
   (--> ((C_1 ... -> any) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        ((C_1 ... --> any) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 (remember-contract V (pred proc? Λ)))
        (side-condition (term (∈ #t (δ (@ proc? V ★)))))
        chk-fun-pass)   
   
   ;; DAMNING
   (--> ((C_1 ... -> any) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (blame ℓ_1 ℓ_3 V-or-AE (C_1 ... -> any) V)
        (side-condition (term (∈ #f (δ (@ proc? V ★)))))
        chk-fun-fail-flat)))

(test
 (test--> c (term ((nat/c) <= f g (-- 0) f (-- 5))) 
          (term (if (@ (λ (x) #t) (-- 5) Λ)
                    (-- 5)
                    (blame f f (-- 0) (nat/c) (-- 5)))))
 (test--> c #:equiv (λ (x1 x2) (term (≡α ,x1 ,x2)))
          (term ((nat/c) <= f g (-- 0) f (-- (λ (x) x))))
          (term (if (@ (λ (x) #f) (-- (λ (x) x)) Λ)
                    (-- (λ (x) x))
                    (blame f f (-- 0) (nat/c) (-- (λ (x) x))))))
 (test--> c 
          (term ((nat/c) <= f g (-- 0) f (-- #t))) 
          (term (if (@ (λ (x) #f) (-- #t) Λ)
                    (-- #t)
                    (blame f f (-- 0) (nat/c) (-- #t)))))
 (test--> c
          (term (((any/c)  -> (any/c)) <= f g (-- 0) f (-- (λ (x) x))))
          (term (((any/c)  --> (any/c)) <= f g (-- 0) f (-- (λ (x) x)))))
 (test--> c 
          (term (((any/c)  -> (any/c)) <= f g (-- 0) f (-- 5)))
          (term (blame f f (-- 0) ((any/c) -> (any/c)) (-- 5))))
 (test--> c #:equiv (λ (x1 x2) (term (≡α ,x1 ,x2)))
          (term ((pred (λ (x) 0) ℓ) <= f g (-- 0) f (-- 5)))
          (term (if (@ (λ (x) (@ (λ (x) 0) x ℓ)) (-- 5) Λ)
                    (-- 5 (pred (λ (x) 0) ℓ))
                    (blame f f (-- 0) (pred (λ (x) 0) ℓ) (-- 5)))))
 (test--> c
          (term ((and/c (nat/c) (empty/c)) <= f g (-- 0) f (-- #t)))
          (term (if (@ (λ (x) #f)
                       (-- #t)
                       Λ)
                    (-- #t)
                    (blame f f (-- 0) (and/c (pred nat? Λ) (pred empty? Λ)) (-- #t))))))
               
(define c~
  (reduction-relation
   λc~ #:domain E
   
   ;; applying abstract values to concrete values
   (--> (@ AV V ... ℓ)
        ;; do bad things in case of a concrete value
        (amb E_result
             (begin (demonic* C_demon V_demon) E_result) ...)
        (side-condition (term (∈ #t (δ (@ proc? AV ★)))))
        (side-condition (equal? (length (term (V ...)))
                                (term (arity AV))))
        (where (-- C ...) AV) ;; Intentionally doesn't match blessed-AV.
        (where ((C_D ...) ..._1) (domain-contracts (C ...)))        
        (where (C_demon ..._1) ((∧ C_D ...) ...))        
        (where (V_demon ..._1) (V ...))
        (where (C_0 ...) (range-contracts (C ...) (V ...)))
        ;; abstract value constrained by all possible domains
        (where E_result (remember-contract (-- (any/c)) C_0 ...))
        apply-abs-known-arity)
   
   (--> (@ AV V ... ℓ)
        ;; do bad things in case of a concrete value
        (amb (-- (any/c))
             (begin (demonic* (any/c) V) (-- (any/c)))
             ...)
        (where (-- C ...) AV) ;; Intentionally doesn't match blessed-AV.
        (side-condition (term (∈ #t (δ (@ proc? AV ★)))))
        (side-condition (not (term (arity AV))))
        apply-abs-no-arity)
   
   ;; CONTRACT CHECKING OF ABSTRACT VALUES
   
   ;; Predicate contracts are handled by concrete transition.
   
   ;; skip first-order checks that we know this value to have already
   ;; passed higher-order checks impose obligations on people we
   ;; interact with, so they must be kept around also, higher-order
   ;; checks could fail later even if they passed earlier

   ;; FIXME: if we add state, then we can't remember stateful predicates or 
   ;; predicates on stateful values   
   
   ;; SPLITTING OR/C and REC/C ABSTRACT VALUES
   ;; Some introduced values are infeasible, which is still sound.
   (--> (-- C_0 ... (or/c C_1 ... C_2 C_3 ...) C ...)
        (remember-contract (-- (any/c) C_0 ... C ...) C_2)
        (side-condition (term (valid? C_2)))
        abs-or/c-split)
   
   (--> (-- C_0 ... (rec/c x C_1) C ...)  ;; Productivity implies this doesn't loop.
        (remember-contract (-- (any/c) C_0 ... C ...)  (unroll (rec/c x C_1)))
        (side-condition (term (valid? (rec/c x C_1))))
        abs-rec/c-unroll)))

;; modulename x valuename x modules -> value
(define-metafunction λc~
  lookup-modref/val : f f (M ...) -> PV or bullet
  [(lookup-modref/val f f_1 (M ... 
                             (module f LANG R DEF ... (define f_1 any_result) DEF_1 ... any_p)
                             M_1 ...))
   any_result]
  [(lookup-modref/val f f_1 any)
   ,(format "unbound module variable ~a from ~a" (term f_1) (term f))])

;; modulename x valuename x modules -> contract
(define-metafunction λc~
  lookup-modref/con : f f (M ...) -> C
  [(lookup-modref/con f f_1 (M ... 
                             (module f LANG R DEF ...(provide/contract any_1 ... [f_1 C] any_2 ...))
                             M_1 ...))
   C]
  [(lookup-modref/con f f_1 any)
   (pred (λ (x) ,(format "unbound module variable ~a from ~a" (term f_1) (term f))) ★)])
   
   
  
(define (∆ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f_1 ^ f f)
        (-- PV)
        (where PV (lookup-modref/val f f_1 ,Ms))        
        Δ-self)
   (--> (f_1 ^ ℓ f)
        (C <= f ℓ (-- PV) f_1 (-- PV))
        (where C (lookup-modref/con f f_1 ,Ms))
        (where PV (lookup-modref/val f f_1 ,Ms))
        (side-condition (not (eq? (term f) (term ℓ))))
        Δ-other)))

(test
 (test--> (∆ (term [(module f racket (require) (define v 0) (provide/contract [v (any/c)]))]))
          (term (v ^ f f))
          (term (-- 0)))
 (test--> (∆ (term [(module f racket (require) (define v 0) (provide/contract [v (any/c)]))]))
          (term (v ^ g f))
          (term ((any/c) <= f g (-- 0) v (-- 0)))))

(define (Δ~ Ms)
  (union-reduction-relations
   (∆ Ms)
   (reduction-relation
    λc~ #:domain E
    (--> (f_1 ^ ℓ f)
         (C <= f ℓ (-- C) f_1 (remember-contract (-- (any/c)) C))
         (where bullet (lookup-modref/val f f_1 ,Ms))
         (where C (lookup-modref/con f f_1 ,Ms))
         (side-condition (not (eq? (term f) (term ℓ))))
         ∆-opaque))))

(test
 (test--> (context-closure (Δ~ (term [(simple-module prime? (any/c) ☁)])) λc~ 𝓔)
          (term (@ (prime? ^ rsa prime?)
                   (-- (pred (prime? ^ keygen prime?) keygen)) Λ))         
          (term (@ ((any/c) <= prime? rsa (-- (any/c)) prime? (-- (any/c)))
                   (-- (pred (prime? ^ keygen prime?) keygen)) Λ)))
 
 (test--> (Δ~ (term [(simple-module prime? (any/c) ☁)]))
          (term (prime? ^ rsa prime?))
          (term ((any/c) <= prime? rsa (-- (any/c)) prime? (-- (any/c)))))
 
 (test--> (Δ~ (term [(simple-module f (any/c) ☁)]))
          (term (f ^ g f))
          (term ((any/c) <= f g (-- (any/c)) f (-- (any/c))))))

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
  (match (apply-reduction-relation (-->_vcc~Δ (program-modules p))
                                   (last p))
    [(list e) (append (program-modules p) (list e))]))

(define-syntax-rule (test-->>p p e ...)
  (test-->> (-->_vcc~Δ (program-modules p))
            #:equiv (λ (e0 e1) (term (≡α ,e0 ,e1)))
            (last p)
            e ...))

(define none/c (term (pred (λ (x) #f) Λ)))

(test 
 (test-->>p (term [(require) (@ (λ () 4) f)]) (term (-- 4)))
 (test-->>p (term [(require) (@ (λ z () 4) f)]) (term (-- 4)))
 (test-->>p (term [(require) (@ (-- (-> (nat/c))) f)]) (term (-- (nat/c))))
 
 ;; testing demonic
 (test-->>p (term (ann [(simple-module p ((cons/c nat? nat?) -> nat?) ☁)
                        (require (only-in p p))
                        (p (cons 1 2))]))
            (term (-- (pred nat? p)))) 
 (test-->>p (term (ann [(simple-module p ((and/c nat? nat?) -> nat?) ☁)
                        (require (only-in p p))
                        (p 1)]))
            (term (-- (pred nat? p))))
 (test-->>p (term (ann [(simple-module p ((or/c nat? nat?) -> nat?) ☁)
                        (require (only-in p p))
                        (p 1)]))
            (term (-- (pred nat? p)))) 
 (test-->>p (term [(require) ((string/c) <= |†| rsa (-- "Plain") rsa (-- "Plain"))])
            (term (-- "Plain"))) 
 #; ;; this depends on unbound modvars sticking instead of erroring
 (test-->>p (term [(require) (@ (-- (λ (o) (b ^ o b))) (-- "") sN)])
            (term (b ^ o b))) 
 (test-->>p (term [(require) (@ (-- (λ (o) (@ 4 5 o))) (-- "") sN)])
            (term (blame o Λ (-- 4) λ (-- 4)))) 
 (test-->>p (term (ann [(simple-module n (and/c nat? nat?) 1) (require (only-in n n)) n]))
            (term (-- 1))) 
 (test-->>p (term (ann [(simple-module n (and/c nat? (pred (λ (x) (= x 7)))) 7) (require (only-in n n)) n]))
            (term (-- 7 (pred (λ (x) (@ = x 7 n)) n)))) 
 (test-->>p (term (ann [(simple-module n (and/c nat? (pred (λ (x) (= x 8)))) 7) (require (only-in n n)) n]))
            (term (blame n n (-- 7) (and/c (pred nat? n) (pred (λ (x) (@ = x 8 n)) n)) (-- 7))))
 (test-->>p (term (ann [(simple-module n (and/c nat? (pred (λ (x) (= x 8)))) "7") (require (only-in n n)) n]))
            (term (blame n n (-- "7") (and/c (pred nat? n) (pred (λ (x) (@ = x 8 n)) (require (only-in n n)) n)) (-- "7"))))
 (test-->>p fit-example (term (-- (pred string? rsa))))
 (test-->>p fit-example-keygen-string
            (term (blame keygen prime? (-- "Key") (pred nat? prime?) (-- "Key"))))
 (test-->>p fit-example-rsa-7
            (term (-- (pred string? rsa)))
            (term (blame keygen keygen (-- (λ (x) 7)) (pred (prime? ^ keygen prime?) keygen) (-- 7)))) 
 (test-->>p example-8 (term (blame h g (-- #f) (pred (λ (x) x) g) (-- #f))))
 (test-->>p example-8-opaque 
            (term (-- (any/c)))
            (term (blame h g (-- (any/c)) (pred (λ (x) x) g) (-- (any/c)))))
 (test-->>p list-id-example (term (-- (cons (-- 1) 
                                            (-- (cons (-- 2) 
                                                      (-- (cons (-- 3) (-- empty))))))))) 
 (test-->>p (term (ann ,list-rev-example-raw))
            (term (-- (cons (-- 3)
                            (-- (cons (-- 2)
                                      (-- (cons (-- 1)
                                                (-- empty)))))))))
 
 ;; Not sure about the remembered contracts in these examples. 
 (test-->>p (term (ann [(simple-module n nat? 5) (require (only-in n n)) n]))
            (term (-- 5))) 
 (test-->>p (term (ann [(simple-module p
                          (cons/c nat? nat?)
                          (cons (-- 1) (-- 2)))
                        (require (only-in p p))
                        p]))
            (term (-- (cons (-- 1) (-- 2)) 
                      (cons/c (pred nat? p) (pred nat? p)))))
 (test-->>p (term (ann [(simple-module p
                          (pred (λ (x) (if (cons? x)
                                           (= (first x)
                                              (rest x))
                                           #f)))
                          (cons (-- 1) (-- 1)))
                        (require (only-in p p))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (pred (λ (x) (if (@ cons? x p)
                                       (@ = 
                                          (@ first x p)
                                          (@ rest x p)
                                          p)
                                       #f))
                            p))))
 (test-->>p (term (ann [(simple-module p
                          (and/c (cons/c nat? nat?)
                                 (pred (λ (x) (= (first x) (rest x)))))
                          (cons (-- 1) (-- 1)))
                        (require (only-in p p))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (cons/c (pred nat? p) (pred nat? p)) 
                      (pred (λ (x) (@ = (@ first x p) (@ rest x p) p)) p))))
 
 ;; Swap of and/c arguments above
 (test-->>p (term (ann [(simple-module p
                          (and/c (pred (λ (x) (= (first x) (rest x))))
                                 (cons/c nat? nat?))                                
                          (cons (-- 1) (-- 1)))
                        (require (only-in p p))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (pred (λ (x) (@ = (@ first x p) (@ rest x p) p)) p)
                      (cons/c (pred nat? p) (pred nat? p)))))
 
 (test-->>p (term (ann [(simple-module p
                          (cons/c nat? nat?)
                          (cons (-- 1) (-- 2)))
                        (require (only-in p p))
                        (first p)]))
            (term (-- 1)))
 (test-->>p (term (ann [(simple-module p
                          (cons/c nat? nat?)
                          (cons (-- "hi") (-- 2)))
                        (require (only-in p p))
                        (first p)]))
            (term (blame p p 
                         (-- (cons (-- "hi") (-- 2)))
                         (cons/c (pred nat? p) (pred nat? p))
                         (-- (cons (-- "hi") (-- 2))))))
 
 (test-->>p (term (ann [(simple-module p
                          (cons/c (anything -> nat?) anything)
                          (cons (-- (λ (x) "hi"))
                                (-- 7)))
                        (require (only-in p p))
                        ((first p) 7)]))
            (term (blame p p (-- (cons (-- (λ (x) "hi"))
                                       (-- 7)))
                         (pred nat? p)
                         (-- "hi"))))

 
 (test-->>p (term [(simple-module mt (pred empty? mt) empty) (require (only-in mt mt)) (mt ^ † mt)])
            (term (-- empty)))
 
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
