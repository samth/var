#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide v)
(test-suite test step-v)

(define v
  (reduction-relation
   λcρ #:domain (D σ)
   (--> (PREVAL σ) ((-- PREVAL) σ) wrap)
   ;; Environment propagation
   (--> ((clos (@ EXP ... LAB) ρ) σ)
        ((@ (clos EXP ρ) ... LAB) σ)
        ρ-@)
   (--> ((clos (if EXP ...) ρ) σ)
        ((if (clos EXP ρ) ...) σ)
        ρ-if)
   (--> ((clos (let ((X EXP_1) ...) EXP_2) ρ) σ)
        ((let ((X (clos EXP_1 ρ)) ...) (clos EXP_2 ρ)) σ)
        ρ-let)
   (--> ((clos (begin EXP ...) ρ) σ)
        ((begin (clos EXP ρ) ...) σ)
        ρ-begin)
   ;; Environment elimination
   (--> ((clos MODREF ρ) σ) (MODREF σ) elim-ρ)
   ;; Variable lookup
   (--> ((clos X ρ) σ)
        (V σ)
        (where (any_0 ... V any_1 ...) (deref σ (env-lookup ρ X)))
        var)
   ;; Application
   (--> ((@ (-- (clos (λ (X ..._1) EXP) ρ) C* ...) V ..._1 LAB) σ)
        ((clos EXP (extend-env* ρ (X a) ...))
         (extend-sto* σ (a (V)) ...))
        (where (a ...) (alloc σ (X ...)))
        β)   
   (--> ((@ (-- (clos (λ F (X ..._1) EXP) ρ) C* ...) V ..._1 LAB) σ)         
        ((clos EXP (extend-env* ρ (F a_0) (X a) ...))
         (extend-sto* σ 
                      (a_0 ((-- (clos (λ F (X ...) EXP) ρ) C* ...)))
                      (a (V))
                      ...))
        (where (a_0 a ...) (alloc σ (F X ...)))           
        β-rec)
   
   ;; Handle first class operations.     
   (--> ((@ V U ... LAB) σ)
        ((blame LAB Λ V λ V) σ)
        (side-condition (term (∈ #t (δ procedure? V ★))))
        (side-condition (term (∈ #f (δ procedure-arity-includes? 
                                       V 
                                       (-- (clos ,(length (term (U ...))) (env)))
                                       ★))))
        wrong-arity)   
   (--> ((@ V U ... LAB) σ)
        ((blame LAB Λ V λ V) σ)
        (side-condition (term (∈ #f (δ procedure? V ★))))
        wrong-not-proc)
   (--> ((if V D_1 D_2) σ) (D_1 σ)
        (side-condition (term (∈ #f (δ false? V ★))))
        if-t)  
   (--> ((if V D_1 D_2) σ) (D_2 σ)
        (side-condition (term (∈ #t (δ false? V ★))))
        if-f)
   (--> ((@ (-- (clos OP ρ) C ...) V ... LAB) σ)
        (A σ)
        (where (A_1 ... A A_2 ...)
               (δ OP V ... LAB))
        δ)
  
   (--> ((begin V D) σ) (D σ) begin)
   (--> ((let ((X V) ...) (clos EXP ρ)) σ)
        ((clos EXP (extend-env* ρ (X a) ...))
         (extend-sto* σ (a (V)) ...))
        (where (a ...) (alloc σ (X ...)))
        let)))

(test
 (define -->_v 
   (reduction-relation 
    λcρ 
    (--> ((in-hole 𝓔 D_redex) σ)
         ((in-hole 𝓔 D_contractum) σ_1)
         (where (any_0 ... (D_contractum σ_1) any_1 ...)
                ,(apply-reduction-relation v (term (D_redex σ)))))))
 (test/σ--> v 
          (term (clos (@ (λ (x) 0) 1 †) (env)))
          (term (@ (clos (λ (x) 0) (env)) (clos 1 (env)) †))) 
 (test/σ--> v
          (term (clos (λ (x) 0) (env)))
          (term (-- (clos (λ (x) 0) (env)))))
 (test/σ--> v
          (term (clos 1 (env)))
          (term (-- (clos 1 (env)))))
 (test--> v
          (term ((@ (-- (clos (λ (x) 0) (env))) (-- (clos 1 (env))) †) (sto)))
          (redex-let* λcρ
                      ([(a) (term (alloc (sto) (x)))]) 
                      (term ((clos 0 (extend-env (env) x a))
                             (extend-sto (sto) a ((-- (clos 1 (env)))))))))
 (test/σ--> v
          (term (clos 0 (env)))
          (term (-- (clos 0 (env)))))
  
 (test-->> -->_v
           (term ((clos (@ (λ (x) 0) 1 †) (env)) (sto)))
           (redex-let λcρ
                      ([(a) (term (alloc (sto) (x)))])
                      (term ((-- (clos 0 (extend-env* (env) (x a))))
                             (extend-sto* (sto)
                                          (a ((-- (clos 1 (env))))))))))
 (test--> v
          (term ((@ (-- (clos (λ f (x) (@ f x f)) (env)))
                    (-- (clos 0 (env)))
                    f)
                 (sto)))
          (redex-let λcρ
                     ([(a_f a_x) (term (alloc (sto) (f x)))])
                     (term ((clos (@ f x f) 
                                 (extend-env* (env)
                                              (f a_f)
                                              (x a_x)))
                            (extend-sto* (sto)
                                         (a_f ((-- (clos (λ f (x) (@ f x f)) (env)))))
                                         (a_x ((-- (clos 0 (env))))))))))

 (test/v-->> -->_v
             (term (clos (@ (λ fact (n)
                              (if (@ zero? n †)
                                  1
                                  (@ * n (@ fact (@ sub1 n †) †) †)))
                            5 †)
                         (env)))
             (term (-- (clos 120 (env)))))
                        
 (test--> v
          (term ((clos x (env (x 0))) (sto (0 ((-- (clos 2 (env))))))))
          (term ((-- (clos 2 (env))) (sto (0 ((-- (clos 2 (env))))))))) 
 (test/σ--> v
          (term (clos (if #f 7 8) (env)))
          (term (if (clos #f (env)) (clos 7 (env)) (clos 8 (env))))) 
 (test/σ--> v
          (term (clos #f (env)))
          (term (-- (clos #f (env))))) 
 (test/σ--> v
          (term (if (-- (clos #f (env)))
                    (clos 7 (env))
                    (clos 8 (env))))
          (term (clos 8 (env))))
 (test/σ--> v
          (term (if (-- (clos #t (env)))
                    (clos 7 (env))
                    (clos 8 (env))))
          (term (clos 7 (env))))
 (test/σ--> v
          (term (@ (-- (clos string=? (env))) 
                   (-- (clos "foo" (env)))
                   (-- (clos "foo" (env))) 
                   †))
          (term (-- (clos #t (env)))))
 (test/σ--> v
          (term (@ (-- (clos expt (env)))
                   (-- (clos 2 (env)))
                   (-- (clos 32 (env)))
                   †))
          (term (-- (clos 4294967296 (env)))))
 (test/σ--> v
          (term (@ (-- (clos + (env)))
                   (-- (clos "foo" (env))) 
                   (-- (clos 7 (env)))
                   †))
          (term (blame † Λ (-- (clos "foo" (env))) + (-- (clos "foo" (env))))))
 (test/σ--> v 
          (term (begin (-- (clos 3 (env))) (clos 5 (env))))
          (term (clos 5 (env))))  
 (test-->> -->_v
           (term ((clos (begin 3 5) (env)) (sto)))
           (term ((-- (clos 5 (env))) (sto))))
 (test--> v
          (term ((let ((x (-- (clos 1 (env))))
                       (y (-- (clos 2 (env)))))
                   (clos (@ + x y †) (env)))
                 (sto)))
          (redex-let λcρ
                     ([(a_0 a_1) (term (alloc (sto) (x y)))])                     
                     (term ((clos (@ + x y †)
                                  (extend-env* (env) (x a_0) (y a_1)))
                            (extend-sto* (sto) 
                                         (a_0 ((-- (clos 1 (env)))))
                                         (a_1 ((-- (clos 2 (env))))))))))
  (test-->> -->_v
            (term ((let ((x (-- (clos 1 (env))))
                         (y (-- (clos 2 (env)))))
                     (clos (@ + x y †) (env)))
                   (sto)))
            (redex-let λcρ
                       ([(a_x a_y) (term (alloc (sto) (x y)))])  
                       (term ((-- (clos 3 (env))) 
                              (extend-sto* (sto) 
                                           (a_x ((-- (clos 1 (env)))))
                                           (a_y ((-- (clos 2 (env))))))))))    
  (test-->> -->_v
            (term ((clos (let ((x 1) (y 2)) (@ + x y †)) (env)) (sto)))
            (redex-let λcρ
                       ([(a_x a_y) (term (alloc (sto) (x y)))])
                       (term ((-- (clos 3 (env)))
                              (extend-sto* (sto) 
                                           (a_x ((-- (clos 1 (env)))))
                                           (a_y ((-- (clos 2 (env))))))))))
  
  (test-->> -->_v
            (term ((clos (@ procedure-arity-includes? (λ (x) x) 1 †) (env)) (sto)))
            (term ((-- (clos #t (env))) (sto))))
  (test-->> -->_v
            (term ((clos (@ procedure-arity-includes? (λ (x) x) 2 †) (env)) (sto)))
            (term ((-- (clos #f (env))) (sto))))
  (test-->> -->_v
            (term ((clos (@ (λ () 1) 2 †) (env)) (sto)))
            (term ((blame † Λ (-- (clos (λ () 1) (env))) λ (-- (clos (λ () 1) (env)))) (sto))))
  (test-->> -->_v
            (term ((clos (@ 3 1 †) (env)) (sto)))
            (term ((blame † Λ (-- (clos 3 (env))) λ (-- (clos 3 (env)))) (sto)))))

