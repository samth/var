#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide c~)
(test-suite test step-c-abs)

(define c~
  (reduction-relation
   λcρ #:domain (D σ)
      
   ;; applying abstract values to concrete values
   (--> ((@ AV V ... LAB) σ)        
        (D σ) ;; do bad things in case of a concrete value
        (where (-- C ...) AV) ;; Intentionally doesn't match blessed-AV.
        (side-condition (term (∈ #t (δ procedure? AV))))
        (side-condition (term (∈ #t (δ procedure-arity-includes? AV (-- (↓ ,(length (term (V ...))) (env)))))))                        
        (where (((CON_D ρ_D) ..._1) ...) (domain-contracts (C ...) (V ...)))
        (where (CON_demon ..._1) ((∧ CON_D ...) ...))
        (where (V_demon ..._1) (V ...))
        (where (D_1 ... D D_2 ...) ((dem (CON_demon V_demon)) ...))
        apply-abs-known-arity-demonic)
   
   (--> ((@ AV V ... LAB) σ)        
        ((join-contracts C_0 ...) σ)
        (where (-- C ...) AV) ;; Intentionally doesn't match blessed-AV.
        (side-condition (term (∈ #t (δ procedure? AV))))
        (side-condition (term (∈ #t (δ procedure-arity-includes? AV (-- (↓ ,(length (term (V ...))) (env)))))))        
        (where (C_0 ...) (range-contracts (C ...) (V ...)))
        apply-abs-known-arity-sucess)))             
