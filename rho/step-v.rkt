#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide v)
(test-suite test step-v)

(define v
  (reduction-relation
   λcρ #:domain D
   (--> PREVAL (-- PREVAL) wrap)
   ;; Environment propagation
   (--> (clos (@ EXP ... LAB) ρ)
        (@ (clos EXP ρ) ... LAB)
        ρ-@)
   (--> (clos (if EXP ...) ρ)
        (if (clos EXP ρ) ...)
        ρ-if)
   (--> (clos (let ((X EXP_1) ...) EXP_2) ρ)
        (let ((X (clos EXP_1 ρ)) ...) (clos EXP_2 ρ))
        ρ-let)
   (--> (clos (begin EXP ...) ρ)
        (begin (clos EXP ρ) ...)
        ρ-begin)
   ;; Environment elimination
   (--> (clos MODREF ρ) MODREF elim-ρ)
   ;; Variable lookup
   (--> (clos X ((X_1 V_1) ... (X V) (X_2 V_2) ...))
        V
        var)
   ;; Application
   (--> (@ (-- (clos (λ (X ..._1) EXP) ρ) C* ...) V ..._1 LAB)
        (clos EXP (env-extend ρ (X V) ...))
        β)   
   (--> (@ (-- (clos (λ F (X ..._1) EXP) ρ) C* ...) V ..._1 LAB)
        (clos EXP (env-extend ρ (F (-- (clos (λ F (X ...) EXP) ρ) C* ...)) (X V) ...))
        β-rec)
   
   ;; Handle first class operations.     
   (--> (@ V U ... LAB)
        (blame LAB Λ V λ V)
        (side-condition (term (∈ #t (δ procedure? V ★))))
        (side-condition (term (∈ #f (δ procedure-arity-includes? 
                                       V 
                                       (-- (clos ,(length (term (U ...))) ()))
                                       ★))))
        wrong-arity)   
   (--> (@ V U ... LAB)
        (blame LAB Λ V λ V)
        (side-condition (term (∈ #f (δ procedure? V ★))))
        wrong-not-proc)
   (--> (if V D_1 D_2) D_1
        (side-condition (term (∈ #f (δ false? V ★))))
        if-t)  
   (--> (if V D_1 D_2) D_2
        (side-condition (term (∈ #t (δ false? V ★))))
        if-f)
   (--> (@ (-- (clos OP ρ) C ...) V ... LAB)
        A
        (where (A_1 ... A A_2 ...)
               (δ OP V ... LAB))
        δ)
  
   (--> (begin V D) D begin)
   (--> (let ((X V) ...) (clos EXP ρ))
        (clos EXP (env-extend ρ (X V) ...))
        let)))



(test
 (define -->_v (context-closure v λcρ 𝓔))
 (test--> v 
          (term (clos (@ (λ (x) 0) 1 †) ()))
          (term (@ (clos (λ (x) 0) ()) (clos 1 ()) †))) 
 (test--> v
          (term (clos (λ (x) 0) ()))
          (term (-- (clos (λ (x) 0) ()))))
 (test--> v
          (term (clos 1 ()))
          (term (-- (clos 1 ()))))
 (test--> v
          (term (@ (-- (clos (λ (x) 0) ())) (-- (clos 1 ())) †))
          (term (clos 0 ((x (-- (clos 1 ())))))))
 (test--> v
          (term (clos 0 ((x (-- (clos 1 ()))))))
          (term (-- (clos 0 ((x (-- (clos 1 ()))))))))
 (test-->> -->_v
           (term (clos (@ (λ (x) 0) 1 †) ()))
           (term (-- (clos 0 ((x (-- (clos 1 ()))))))))
 
 (test-->> -->_v
           (term (clos (@ (λ fact (n)
                            (if (@ zero? n †)
                                1
                                (@ * n (@ fact (@ sub1 n †) †) †)))
                          5 †)
                       ()))
           (term (-- (clos 120 ()))))
                        
 (test--> v
          (term (clos x ((x (-- (clos 2 ()))))))
          (term (-- (clos 2 ()))))
 (test--> v
          (term (clos (if #f 7 8) ()))
          (term (if (clos #f ()) (clos 7 ()) (clos 8 ()))))
 (test--> v
          (term (clos #f ()))
          (term (-- (clos #f ()))))
 (test--> v
          (term (if (-- (clos #f ()))
                    (clos 7 ())
                    (clos 8 ())))
          (term (clos 8 ())))
 (test--> v
          (term (if (-- (clos #t ()))
                    (clos 7 ())
                    (clos 8 ())))
          (term (clos 7 ()))) 
 (test--> v
          (term (@ (-- (clos string=? ())) 
                   (-- (clos "foo" ()))
                   (-- (clos "foo" ())) 
                   †))
          (term (-- (clos #t ()))))
 (test--> v
          (term (@ (-- (clos expt ()))
                   (-- (clos 2 ()))
                   (-- (clos 32 ()))
                   †))
          (term (-- (clos 4294967296 ()))))
 (test--> v
          (term (@ (-- (clos + ()))
                   (-- (clos "foo" ())) 
                   (-- (clos 7 ()))
                   †))
          (term (blame † Λ (-- (clos "foo" ())) + (-- (clos "foo" ())))))
 (test--> v 
          (term (begin (-- (clos 3 ())) (clos 5 ())))
          (term (clos 5 ())))
 (test-->> -->_v
           (term (clos (begin 3 5) ()))
           (term (-- (clos 5 ()))))
 (test--> v
          (term (let ((x (-- (clos 1 ())))
                      (y (-- (clos 2 ()))))
                  (clos (@ + x y †) ())))
          (term (clos (@ + x y †)
                      ((x (-- (clos 1 ())))
                       (y (-- (clos 2 ())))))))
  (test-->> -->_v
            (term (let ((x (-- (clos 1 ())))
                        (y (-- (clos 2 ()))))
                    (clos (@ + x y †) ())))
            (term (-- (clos 3 ()))))
  (test-->> -->_v
            (term (clos (let ((x 1) (y 2)) (@ + x y †)) ()))
            (term (-- (clos 3 ()))))
  (test-->> -->_v
            (term (clos (@ procedure-arity-includes? (λ (x) x) 1 †) ()))
            (term (-- (clos #t ()))))
  (test-->> -->_v
            (term (clos (@ procedure-arity-includes? (λ (x) x) 2 †) ()))
            (term (-- (clos #f ()))))
  (test-->> -->_v
            (term (clos (@ (λ () 1) 2 †) ()))
            (term (blame † Λ (-- (clos (λ () 1) ())) λ (-- (clos (λ () 1) ())))))
  (test-->> -->_v
            (term (clos (@ 3 1 †) ()))
            (term (blame † Λ (-- (clos 3 ())) λ (-- (clos 3 ()))))))