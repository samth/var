#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "flat-check.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test step)

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

(define -->_v (context-closure v λcρ 𝓔))

(define-metafunction λcρ
  env-extend : ρ (X V) ... -> ρ
  [(env-extend ((X_1 V_1) ...) (X_2 V_2) ...)
   ((X_2 V_2) ... (X_1 V_1) ...)])

(test
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

(define c
  (reduction-relation
   λcρ #:domain D
   
   ;; FLAT CONTRACTS   
   (--> (FLAT ρ <= LAB_1 LAB_2 V_1 LAB_3 V)  ; FIXME: first V_1 was V-or-AE
        (if (@ (flat-check (FLAT ρ) V) V Λ)
            (remember-contract V (FLAT ρ))
            (blame LAB_1 LAB_3 V_1 (FLAT ρ) V))
        flat-check)

   ))
   #|   
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
        ((C_1 ... --> any) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 (remember-contract V (pred procedure? Λ)))
        (side-condition (term (∈ #t (δ (@ procedure? V ★)))))
        chk-fun-pass)   
   
   ;; DAMNING
   (--> ((C_1 ... -> any) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)
        (blame ℓ_1 ℓ_3 V-or-AE (C_1 ... -> any) V)
        (side-condition (term (∈ #f (δ (@ procedure? V ★)))))
        chk-fun-fail-flat)))

|#

(test
 (test--> c ; (nat? <= 5)   -- provable
          (term ((pred exact-nonnegative-integer? f) () <= f g (-- (clos 0 ())) f (-- (clos 5 ()))))
          (term (if (@ (-- (clos (λ (x) #t) ())) (-- (clos 5 ())) Λ)
                    (remember-contract (-- (clos 5 ())) ((pred exact-nonnegative-integer? f) ()))
                    (blame f f (-- (clos 0 ())) ((pred exact-nonnegative-integer? f) ()) (-- (clos 5 ()))))))
 (test--> c ; (prime? <= 5)   -- runable
          (term ((pred (prime? ^ h j) f) () <= f g (-- (clos 0 ())) f (-- (clos 5 ()))))
          (term (if (@ (-- (clos (λ (x) (@ (prime? ^ h j) x f)) ())) (-- (clos 5 ())) Λ)
                    (remember-contract (-- (clos 5 ())) ((pred exact-nonnegative-integer? f) ()))
                    (blame f f (-- (clos 0 ())) ((pred (prime? ^ h j) f) ()) (-- (clos 5 ())))))))


(define (∆ Ms)
  (reduction-relation
   λcρ #:domain D
   (--> (X_1 ^ X X)
        (-- (clos VAL ()))
        (where VAL (lookup-modref/val X X_1 ,Ms))
        Δ-self)
   (--> (X_1 ^ LAB X)
        (CON () <= X LAB V X_1 V)
        (where CON (lookup-modref/con X X_1 ,Ms))
        (where VAL (lookup-modref/val X X_1 ,Ms))
        (where V (-- (clos VAL ())))
        (side-condition (not (eq? (term X) (term LAB))))
        Δ-other)))

(test 
 (define Ms 
   (term [(module m racket (require) (define f 1) (provide/contract [f (pred string? m)]))]))
 (test--> (∆ Ms)
          (term (f ^ m m))
          (term (-- (clos 1 ()))))
 (test--> (∆ Ms)
          (term (f ^ † m))
          (term ((pred string? m) () <= m † (-- (clos 1 ())) f (-- (clos 1 ()))))))

 
