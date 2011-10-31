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
   (--> (clos X ρ)
        V
        (where V (env-lookup ρ X))
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
                                       (-- (clos ,(length (term (U ...))) (env)))
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
          (term (clos (@ (λ (x) 0) 1 †) (env)))
          (term (@ (clos (λ (x) 0) (env)) (clos 1 (env)) †))) 
 (test--> v
          (term (clos (λ (x) 0) (env)))
          (term (-- (clos (λ (x) 0) (env)))))
 (test--> v
          (term (clos 1 (env)))
          (term (-- (clos 1 (env)))))
 (test--> v
          (term (@ (-- (clos (λ (x) 0) (env))) (-- (clos 1 (env))) †))
          (term (clos 0 (env (x (-- (clos 1 (env))))))))
 (test--> v
          (term (clos 0 (env (x (-- (clos 1 (env)))))))
          (term (-- (clos 0 (env (x (-- (clos 1 (env)))))))))
 (test-->> -->_v
           (term (clos (@ (λ (x) 0) 1 †) (env)))
           (term (-- (clos 0 (env (x (-- (clos 1 (env)))))))))
 
 (test-->> -->_v
           (term (clos (@ (λ fact (n)
                            (if (@ zero? n †)
                                1
                                (@ * n (@ fact (@ sub1 n †) †) †)))
                          5 †)
                       (env)))
           (term (-- (clos 120 (env)))))
                        
 (test--> v
          (term (clos x (env (x (-- (clos 2 (env)))))))
          (term (-- (clos 2 (env)))))
 (test--> v
          (term (clos (if #f 7 8) (env)))
          (term (if (clos #f (env)) (clos 7 (env)) (clos 8 (env)))))
 (test--> v
          (term (clos #f (env)))
          (term (-- (clos #f (env)))))
 (test--> v
          (term (if (-- (clos #f (env)))
                    (clos 7 (env))
                    (clos 8 (env))))
          (term (clos 8 (env))))
 (test--> v
          (term (if (-- (clos #t (env)))
                    (clos 7 (env))
                    (clos 8 (env))))
          (term (clos 7 (env)))) 
 (test--> v
          (term (@ (-- (clos string=? (env))) 
                   (-- (clos "foo" (env)))
                   (-- (clos "foo" (env))) 
                   †))
          (term (-- (clos #t (env)))))
 (test--> v
          (term (@ (-- (clos expt (env)))
                   (-- (clos 2 (env)))
                   (-- (clos 32 (env)))
                   †))
          (term (-- (clos 4294967296 (env)))))
 (test--> v
          (term (@ (-- (clos + (env)))
                   (-- (clos "foo" (env))) 
                   (-- (clos 7 (env)))
                   †))
          (term (blame † Λ (-- (clos "foo" (env))) + (-- (clos "foo" (env))))))
 (test--> v 
          (term (begin (-- (clos 3 (env))) (clos 5 (env))))
          (term (clos 5 (env))))
 (test-->> -->_v
           (term (clos (begin 3 5) (env)))
           (term (-- (clos 5 (env)))))
 (test--> v
          (term (let ((x (-- (clos 1 (env))))
                      (y (-- (clos 2 (env)))))
                  (clos (@ + x y †) (env))))
          (term (clos (@ + x y †)
                      (env (x (-- (clos 1 (env))))
                           (y (-- (clos 2 (env))))))))
  (test-->> -->_v
            (term (let ((x (-- (clos 1 (env))))
                        (y (-- (clos 2 (env)))))
                    (clos (@ + x y †) (env))))
            (term (-- (clos 3 (env)))))
  (test-->> -->_v
            (term (clos (let ((x 1) (y 2)) (@ + x y †)) (env)))
            (term (-- (clos 3 (env)))))
  (test-->> -->_v
            (term (clos (@ procedure-arity-includes? (λ (x) x) 1 †) (env)))
            (term (-- (clos #t (env)))))
  (test-->> -->_v
            (term (clos (@ procedure-arity-includes? (λ (x) x) 2 †) (env)))
            (term (-- (clos #f (env)))))
  (test-->> -->_v
            (term (clos (@ (λ () 1) 2 †) (env)))
            (term (blame † Λ (-- (clos (λ () 1) (env))) λ (-- (clos (λ () 1) (env))))))
  (test-->> -->_v
            (term (clos (@ 3 1 †) (env)))
            (term (blame † Λ (-- (clos 3 (env))) λ (-- (clos 3 (env)))))))