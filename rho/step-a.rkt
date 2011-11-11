#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide a)
(test-suite test step-apply)

(define a
  (reduction-relation
   λcρ #:domain (D σ)
      
   (--> ((clos (apply ^ LAB) ρ) σ)
        ((-- (clos apply ρ)) σ)
        apply-wrap)
        
   (--> ((@ (-- (clos apply ρ)) V LAB) σ)
        ((blame LAB Λ V apply V) σ))
   
   (--> ((@ (-- (clos apply ρ)) V_1 V_2 LAB) σ)        
        ((@ V_1 V ... LAB) σ)
        (where #t (list-value? V_2))
        (where (V ...) (list-value->list V_2)))
   
   ;; Could be expressed as a contract.
   (--> ((@ (-- (clos apply ρ)) V_1 V_2 LAB) σ)        
        ((blame LAB Λ V_2 apply V_2) σ)
        (where #f (list-value? V_2)))))
               
(define-metafunction λcρ
  list-value? : V -> #t or #f
  [(list-value? (-- (clos empty ρ) C ...)) #t]
  [(list-value? (-- (cons V_1 V_2) C ...))
   (list-value? V_2)]
  ;; FIXME not handling abstract values
  [(list-value? V) #f])
  
(define-metafunction λcρ
  list-value->list : V -> (V ...)
  [(list-value->list (-- (clos empty ρ) C ...)) ()]
  [(list-value->list (-- (cons V_1 V_2) C ...))
   ,(cons (term V_1) (term (list-value->list V_2)))])
