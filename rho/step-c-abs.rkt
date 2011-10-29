#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "check.rkt" "util.rkt")
(provide c~)
(test-suite test step-c-abs)

(define c~
  (reduction-relation
   λcρ #:domain D
      
   ;; applying abstract values to concrete values
   (--> (@ AV V ... LAB)
        ;; do bad things in case of a concrete value
        (amb V_result
             (let ((d (demonic* CON_demon V_demon))
                   (r V_result))
               (clos r ())) 
             ...)
        (side-condition (term (∈ #t (δ procedure? AV ★))))
        (where natural (arity AV))
        (side-condition (= (term natural) (length (term (V ...)))))
        
        (where (-- C ...) AV) ;; Intentionally doesn't match blessed-AV.
        (where (((CON_D ρ_D) ..._1) ...) (domain-contracts (C ...)))
        (where (CON_demon ..._1) ((∧ CON_D ...) ...))
        (where (V_demon ..._1) (V ...))
        (where (C_0 ...) (range-contracts (C ...) (V ...)))
        ;; abstract value constrained by all possible domains
        (where V_result (join-contracts C_0 ...))
        apply-abs-known-arity)
      
   (--> (@ AV V ... LAB)
        ;; do bad things in case of a concrete value
        (amb (join-contracts)
             (let ((d (demonic* (∧) V))
                   (r (join-contracts)))
               (clos r ()))
             ...)
        (where (-- C ...) AV) ;; Intentionally doesn't match blessed-AV.
        (side-condition (term (∈ #t (δ procedure? AV ★))))
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
   (--> (-- C_0 ... ((or/c CON_1 ... CON_2 CON_3 ...) ρ) C ...)
        (join-contracts C_0 ... (CON_2 ρ) C ...)
        abs-or/c-split)   
   (--> (-- C_0 ... ((rec/c X CON) ρ) C_1 ...)  ;; Productivity implies this doesn't loop.
        (join-contracts C_0 ... ((unroll (rec/c X CON)) ρ) C_1 ...)
        abs-rec/c-unroll)))

(test 
 (test--> c~
          (term (@ (-- (((pred (even? ^ fun e/o) fun) -> (pred (even? ^ fun e/o) fun)) ()))
                   (-- (clos 4 ())
                       ((pred (even? ^ dbl e/o) dbl) ())
                       ((pred (even? ^ fun e/o) fun) ()))
                   †))
          (term (amb (-- ((pred (even? ^ fun e/o) fun) ())) 
                     (let ((d (-- (clos 0 ()))) 
                           (r (-- ((pred (even? ^ fun e/o) fun) ())))) 
                       (clos r ())))))

 (test--> c~
          (term (@ (-- ((pred procedure? †) ()))
                   (-- (clos 4 ()))
                   †))
          (term (if (-- ((pred boolean? Λ) ()))
                    (-- ((pred (λ (x) #t) Λ) ())) 
                    (let ((d (-- (clos 0 ()))) 
                          (r (-- ((pred (λ (x) #t) Λ) ())))) 
                      (clos r ())))))
 
 (test--> c~
          (term (-- ((or/c (∧) (∧)) ())))
          (term (-- ((∧) ()))))
 (test--> c~
          (term (-- ((or/c (pred (x? ^ f g) f)
                           (pred (y? ^ f g) f))
                     ())))
          (term (-- ((pred (x? ^ f g) f) ())))
          (term (-- ((pred (y? ^ f g) f) ()))))
 (test--> c~
          (term (-- ((rec/c x (cons/c x x)) ())))
          (term (-- ((cons/c (rec/c x (cons/c x x))
                             (rec/c x (cons/c x x)))
                     ())))))
          
                
                
