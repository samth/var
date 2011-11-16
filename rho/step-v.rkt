#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "op.rkt" "util.rkt")
(provide v)
(test-suite test step-v)

(define v
  (reduction-relation
   λcρ #:domain (D σ)
   (--> ((clos • ρ) σ) ((join-contracts) σ) bullet)
   (--> ((clos (OP ^ LAB) ρ) σ)
        (((op-con OP) (env) <= Λ LAB (-- (↓ OP (env))) OP (-- (↓ OP (env)))) σ))
   (--> (PREVAL σ) ((-- PREVAL) σ) wrap)
   ;; Environment propagation
   (--> ((clos (@ EXP ... LAB) ρ) σ)
        ((@ (↓ EXP ρ) ... LAB) σ)
        ρ-@)
   (--> ((clos (if EXP ...) ρ) σ)
        ((if (↓ EXP ρ) ...) σ)
        ρ-if)
   (--> ((clos (let ((X EXP_1) ...) EXP_2) ρ) σ)
        ((let ((X (↓ EXP_1 ρ)) ...) (↓ EXP_2 ρ)) σ)
        ρ-let)
   (--> ((clos (begin EXP ...) ρ) σ)
        ((begin (↓ EXP ρ) ...) σ)
        ρ-begin)
   ;; Environment elimination
   (--> ((clos MODREF ρ) σ) (MODREF σ) elim-ρ)
   ;; Variable lookup
   (--> ((clos X ρ) σ)
        (V σ)
        (where (any_0 ... V any_1 ...) (lookup-var σ ρ X))
        var)
   ;; Application
   (--> ((@ (-- (clos (λ (X ..._1) EXP) ρ) C* ...) V ..._1 LAB) σ)
        ((↓ EXP ρ_1) σ_1)
        (judgment-holds (chooses (V ...) (V_* ...)))
        (where (ρ_1 σ_1) (bind-vars ρ σ (X V_*) ...))        
        β)
   (--> ((@ (-- (clos (λ* (X ..._1 X_r) EXP) ρ) C* ...) V ..._1 V_r ... LAB) σ)
        ((↓ EXP ρ_1) σ_1)
        (judgment-holds (chooses (V ...) (V_* ...)))
        (where (ρ_1 σ_1) (bind-vars ρ σ (X V_*) ... (X_r (list->list-value (V_r ...)))))        
        β*)
   (--> ((@ (-- (clos (λ F (X ..._1) EXP) ρ) C* ...) V ..._1 LAB) σ)        
        ((↓ EXP ρ_1) σ_1)
        (judgment-holds (chooses (V ...) (V_* ...)))
        (where (ρ_1 σ_1)
               (bind-vars ρ σ 
                          (F (-- (↓ (λ F (X ...) EXP) ρ) C* ...)) 
                          (X V_*) ...))
        (side-condition 
         (not (and (redex-match λcρ (AV* ...) (term (V ...)))
                   (redex-match λcρ ((CON_a #hash()) ... ((CON_0 ... -> any_c3) #hash()) (CON_b #hash()) ...) (term (C* ...))))))
        β-rec)
   ;; this rule replaces the recursive call with its abstraction
   (--> ((@ (-- (clos (λ F (X ..._1) EXP) ρ) C* ...) AV* ..._1 LAB) σ)
        ((let ([F ((∧ CON_a ... (CON_0 ... -> any_c3) CON_b ...) (env)
                   <= ★ LAB 
                   (-- (↓ (λ F (X ...) EXP) ρ) C* ...)
                   qqqqqq
                   (-- C* ...))])
           (↓ EXP ρ_1))
         σ_1)
        ;((↓ EXP ρ_1) σ_1)
        (judgment-holds (chooses (AV* ...) (AV*_* ...)))
        (where (ρ_1 σ_1) (bind-vars ρ σ (X AV*_*) ...))
        (where ((CON_a #hash()) ... ((CON_0 ... -> any_c3) #hash()) (CON_b #hash()) ...) (C* ...))
        #;(side-condition (printf "widening ~a\n" (term F)))
        special-β-rec)
   
   
   ;; Handle first class operations.     
   (--> ((@ V U ... LAB) σ)
        ((blame LAB Λ V λ V) σ)
        (side-condition (term (∈ #t (δ procedure? V))))
        (where #f (arity-includes? V ,(length (term (U ...)))))
        wrong-arity)   
   (--> ((@ V U ... LAB) σ)
        ((blame LAB Λ V λ V) σ)
        (side-condition (term (∈ #f (δ procedure? V))))
        wrong-not-proc)
   (--> ((if V D_1 D_2) σ) (D_1 σ)
        (side-condition (term (∈ #f (δ false? V))))
        if-t)  
   (--> ((if V D_1 D_2) σ) (D_2 σ)
        (side-condition (term (∈ #t (δ false? V))))
        if-f)
   (--> ((@ (-- (clos OP ρ) C ...) V ... LAB) σ)
        (A σ)
        (where (A_1 ... A A_2 ...)
               (δ OP V ...))
        δ)
  
   (--> ((begin V D) σ) (D σ) begin)
   (--> ((let ((X V) ...) (clos EXP ρ)) σ)
        ((↓ EXP ρ_1) σ_1)
        (where (ρ_1 σ_1) (bind-vars ρ σ (X V) ...))                
        let)))


(define-judgment-form λcρ
  #:mode (chooses I O)
  #:contract (chooses (V ..._1) (V ..._1))
  [(chooses (V_1 ...) (V_2 ...))
   (choose V_1 V_2)
   ...])

(define-judgment-form λcρ
  #:mode (choose I O)
  #:contract (choose V V)
  [(choose (-- C_1 ... ((or/c CON_1 CON_2) ρ) C_2 ...) V)
   (choose (-- C_1 ... (CON_1 ρ) C_2 ...) V)]
  [(choose (-- C_1 ... ((or/c CON_1 CON_2) ρ) C_2 ...) V)
   (choose (-- C_1 ... (CON_2 ρ) C_2 ...) V)]
  [(choose (-- C_1 ... ((rec/c X CON) ρ) C_2 ...) V)
   (choose (-- C_1 ... ((unroll (rec/c X CON)) ρ) C_2 ...) V)]
  [(choose (-- C# ...) (-- C# ...))]
  [(choose (-- PREVAL C ...) (-- PREVAL C ...))]
  [(choose BLESSED BLESSED)])

(test
 (test-equal (judgment-holds (choose (-- ((or/c (pred boolean? f) (pred string? f)) (env))) V) V)
             (term ((-- ((pred boolean? f) (env)))
                    (-- ((pred string? f) (env))))))
 (test-equal (judgment-holds (choose (-- ((rec/c x (or/c (pred boolean? f) (pred string? f))) (env))) V) V)
             (term ((-- ((pred boolean? f) (env)))
                    (-- ((pred string? f) (env)))))))
 
(test
 (define -->_v 
   (reduction-relation 
    λcρ 
    (--> ((in-hole 𝓔 D_redex) σ)
         ((in-hole 𝓔 D_contractum) σ_1)
         (where (any_0 ... (D_contractum σ_1) any_1 ...)
                ,(apply-reduction-relation v (term (D_redex σ)))))))
 
 (test/σ--> v
            (term (↓ • (env)))
            (term (join-contracts)))
 (test/σ--> v 
          (term (↓ (@ (λ (x) 0) 1 †) (env)))
          (term (@ (↓ (λ (x) 0) (env)) (↓ 1 (env)) †))) 
 (test/σ--> v
          (term (↓ (λ (x) 0) (env)))
          (term (-- (↓ (λ (x) 0) (env)))))
 (test/σ--> v
          (term (↓ 1 (env)))
          (term (-- (↓ 1 (env)))))
 (test/σ--> v
            (term (↓ (let ((x 1) (y 2)) (@ + x y †)) (env)))
            (term (let ((x (↓ 1 (env)))
                        (y (↓ 2 (env))))
                    (↓ (@ + x y †) (env)))))
 (test/σ--> v
            (term (↓ (p? ^ f g) (env)))
            (term (p? ^ f g)))
 (test--> v
          (term ((@ (-- (↓ (λ (x) 0) (env))) (-- (↓ 1 (env))) †) (sto)))
          (redex-let λcρ
                     ([(ρ σ) (term (bind-vars (env) (sto) (x (-- (↓ 1 (env))))))])
                     (term ((↓ 0 ρ) σ))))
 (test/σ--> v
          (term (↓ 0 (env)))
          (term (-- (↓ 0 (env))))) 
 (test-->> -->_v
           (term ((↓ (@ (λ (x) 0) 1 †) (env)) (sto)))
           (redex-let λcρ
                      ([(ρ σ) (term (bind-vars (env) (sto) (x (-- (↓ 1 (env))))))])
                      (term ((-- (↓ 0 ρ)) σ))))
 (test--> v
          (term ((@ (-- (↓ (λ f (x) (@ f x f)) (env)))
                    (-- (↓ 0 (env)))
                    f)
                 (sto)))
          (redex-let λcρ
                     ([(ρ σ) (term (bind-vars (env) (sto) 
                                              (f (-- (↓ (λ f (x) (@ f x f)) (env))))
                                              (x (-- (↓ 0 (env))))))])
                     (term ((↓ (@ f x f) ρ) σ))))                      
 (test/v-->> -->_v
             (term (↓ (@ (λ fact (n)
                              (if (@ zero? n †)
                                  1
                                  (@ * n (@ fact (@ sub1 n †) †) †)))
                            5 †)
                         (env)))
             (term (-- (↓ 120 (env)))))
      
 (redex-let λcρ
            ([(ρ σ) (term (bind-vars (env) (sto) (x (-- (↓ 2 (env))))))])
            (test--> v
                     (term ((↓ x ρ) σ))
                     (term ((-- (↓ 2 (env))) σ))))
 (test/σ--> v
          (term (↓ (if #f 7 8) (env)))
          (term (if (↓ #f (env)) (↓ 7 (env)) (↓ 8 (env))))) 
 (test/σ--> v
          (term (↓ #f (env)))
          (term (-- (↓ #f (env))))) 
 (test/σ--> v
          (term (if (-- (↓ #f (env)))
                    (↓ 7 (env))
                    (↓ 8 (env))))
          (term (↓ 8 (env))))
 (test/σ--> v
          (term (if (-- (↓ #t (env)))
                    (↓ 7 (env))
                    (↓ 8 (env))))
          (term (↓ 7 (env))))
 (test/σ--> v
          (term (@ (-- (↓ string=? (env))) 
                   (-- (↓ "foo" (env)))
                   (-- (↓ "foo" (env))) 
                   †))
          (term (-- (↓ #t (env)))))
 (test/σ--> v
          (term (@ (-- (↓ expt (env)))
                   (-- (↓ 2 (env)))
                   (-- (↓ 32 (env)))
                   †))
          (term (-- (↓ 4294967296 (env)))))
(test/σ--> v 
          (term (begin (-- (↓ 3 (env))) (↓ 5 (env))))
          (term (↓ 5 (env))))  
 (test-->> -->_v
           (term ((↓ (begin 3 5) (env)) (sto)))
           (term ((-- (↓ 5 (env))) (sto))))
 (test--> v
          (term ((let ((x (-- (↓ 1 (env))))
                       (y (-- (↓ 2 (env)))))
                   (↓ (@ + x y †) (env)))
                 (sto)))
          (redex-let λcρ
                     ([(ρ σ) (term (bind-vars (env) (sto) 
                                              (x (-- (↓ 1 (env))))
                                              (y (-- (↓ 2 (env))))))])
                     (term ((↓ (@ + x y †) ρ) σ))))
  (test-->> -->_v
            (term ((let ((x (-- (↓ 1 (env))))
                         (y (-- (↓ 2 (env)))))
                     (↓ (@ + x y †) (env)))
                   (sto)))
            (redex-let λcρ
                      ([(ρ σ) (term (bind-vars (env) (sto) 
                                               (x (-- (↓ 1 (env))))
                                               (y (-- (↓ 2 (env))))))])
                      (term ((-- (↓ 3 (env))) σ))))      
  (test-->> -->_v
            (term ((↓ (@ procedure-arity-includes? (λ (x) x) 1 †) (env)) (sto)))
            (term ((-- (↓ #t (env))) (sto))))
  (test-->> -->_v
            (term ((↓ (@ procedure-arity-includes? (λ (x) x) 2 †) (env)) (sto)))
            (term ((-- (↓ #f (env))) (sto))))
  (test-->> -->_v
            (term ((↓ (@ (λ () 1) 2 †) (env)) (sto)))
            (term ((blame † Λ (-- (↓ (λ () 1) (env))) λ (-- (↓ (λ () 1) (env)))) (sto))))
  (test-->> -->_v
            (term ((↓ (@ 3 1 †) (env)) (sto)))
            (term ((blame † Λ (-- (↓ 3 (env))) λ (-- (↓ 3 (env)))) (sto)))))

