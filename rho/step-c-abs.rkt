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
   
   #|
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
        abs-rec/c-unroll))
|#
   ))

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
                      (clos r ()))))))
                
