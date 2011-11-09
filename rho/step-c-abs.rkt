#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "check.rkt" "util.rkt" "demonic.rkt")
(provide c~)
(test-suite test step-c-abs)

(define c~
  (reduction-relation
   λcρ #:domain (D σ)
      
   ;; applying abstract values to concrete values
   (--> ((@ AV V ... LAB) σ)
        ;; do bad things in case of a concrete value
        ((amb V_result
              (let ((DEMONIC (demonic* CON_demon V_demon))
                    (r V_result))
                (↓ r (env))) 
              ...)
         σ)
        (side-condition (term (∈ #t (δ procedure? AV))))
        (where natural (arity AV))
        (side-condition (= (term natural) (length (term (V ...)))))
        
        (where (-- C ...) AV) ;; Intentionally doesn't match blessed-AV.
        (where (((CON_D ρ_D) ..._1) ...) (domain-contracts (C ...)))
        (where (CON_demon ..._1) ((∧ CON_D ...) ...))
        (where (V_demon ..._1) (V ...))
        (where (C_0 ...) (range-contracts (C ...) (V ...)))
        ;; abstract value constrained by all possible domains
        (where (any_1 ... V_result any_2 ...) (remember-contract/any (-- ((pred (λ (x) #t) Λ) (env))) C_0 ...))
        apply-abs-known-arity)
      
   (--> ((@ AV V ... LAB) σ)
        ;; do bad things in case of a concrete value
        ((amb (join-contracts)
              (let ((DEMONIC (demonic* (∧) V))
                    (r (join-contracts)))
                (↓ r (env)))
              ...)
         σ)
        (where (-- C ...) AV) ;; Intentionally doesn't match blessed-AV.
        (side-condition (term (∈ #t (δ procedure? AV))))
        (side-condition (not (term (arity AV))))
        apply-abs-no-arity)))
     
(test 
 (test/σ--> c~
            (term (@ (-- (((pred (even? ^ fun e/o) fun) -> (pred (even? ^ fun e/o) fun)) (env)))
                     (-- (↓ 4 (env))
                         ((pred (even? ^ dbl e/o) dbl) (env))
                         ((pred (even? ^ fun e/o) fun) (env)))
                     †))
            (term (amb (-- ((pred (even? ^ fun e/o) fun) (env))) 
                       (let ((DEMONIC (-- (↓ 0 (env)))) 
                             (r (-- ((pred (even? ^ fun e/o) fun) (env))))) 
                         (↓ r (env))))))
 
 (test/σ--> c~
            (term (@ (-- ((pred procedure? †) (env)))
                     (-- (↓ 4 (env)))
                     †))
            (term (if (-- ((∧) (env)))
                      (-- ((pred (λ (x) #t) Λ) (env)))
                      (let ((DEMONIC(-- (↓ 0 (env)))) 
                            (r (-- ((pred (λ (x) #t) Λ) (env))))) 
                        (↓ r (env)))))))
