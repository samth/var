#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "check.rkt" "util.rkt")
(provide c)
(test-suite test step-c)

(define c
  (reduction-relation
   λcρ #:domain (D σ)
   
   ;; FLAT CONTRACTS   
   (--> ((FLAT ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)  ; FIXME: first V_1 was V-or-AE
        ((if (@ (-- (clos (flat-check (FLAT ρ) V) (env))) V Λ)
             V_2
             (blame LAB_1 LAB_3 V_1 (FLAT ρ) V))
         σ)
        (where (any_1 ... V_2 any_2 ...) (remember-contract/any V (FLAT ρ)))
        flat-check)
   
   ;; HIGHER-ORDER CONTRACTS   
   (--> (((or/c FLAT HOC) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((if (@ (-- (clos (flat-check (FLAT ρ) V) (env))) V Λ)
             V_2
             (HOC ρ <= LAB_1 LAB_2 V_1 LAB_3 V))
         σ)
        (where (any_1 ... V_2 any_2 ...) (remember-contract/any V (FLAT ρ)))
        or/c-hoc)
   
   (--> (((and/c CON_0 CON_1) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((CON_1 ρ <= LAB_1 LAB_2 V_1 LAB_3 
                (CON_0 ρ <= LAB_1 LAB_2 V_1 LAB_3 V))
         σ)
        (where HOC (and/c CON_0 CON_1))
        and/c-hoc)
   
   (--> (((rec/c X CON) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        (((unroll HOC) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        (where HOC (rec/c X CON))
        unroll-HOC)
   
   ;; PAIR CONTRACTS
   ;; FIXME: forgets what's known about the pair.   
   (--> (((cons/c CON_0 CON_1) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((@ (-- (clos cons (env)))
            (CON_0 ρ <= LAB_1 LAB_2 V_1 LAB_3 V_car)
            (CON_1 ρ <= LAB_1 LAB_2 V_1 LAB_3 V_cdr)
            Λ)
         σ)
        (where HOC (cons/c CON_0 CON_1))
        (where #t (∈ #t (δ cons? V Λ)))
        (where (any_0 ... V_car any_1 ...) (δ car V Λ))
        (where (any_2 ... V_cdr any_3 ...) (δ cdr V Λ))                
        check-cons-pass)
   
   (--> (((cons/c CON_0 CON_1) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((blame LAB_1 LAB_3 V_1 (HOC ρ) V) σ)
        (where HOC (cons/c CON_0 CON_1))
        (where #t (∈ #f (δ cons? V Λ)))
        check-cons-fail)
   
   ;; PROCEDURE CONTRACTS      
   (--> ((@ ((CON_0 ..._1 --> (λ (X ..._1) CON_1)) ρ <= LAB_1 LAB_2 V_2 LAB_3 V) V_1 ..._1 LAB) σ)
        ((CON_1 ρ_1 ; lax
                <= LAB_1 LAB_2 V_2 LAB_3 
                (@ (remember-contract V ((CON_0 ... -> (λ (X ...) CON_1)) ρ))
                   (CON_0 ρ <= LAB_2 LAB_1 V_1 LAB_3 V_1) ... Λ))
         σ_1)
        (where (ρ_1 σ_1) (bind-vars ρ σ (X V_1) ...))
        blessed-β-dep)
   
   (--> ((@ ((CON_0 ..._1 --> CON_1) ρ <= LAB_1 LAB_2 V_2 LAB_3 V) V_1 ..._1 LAB) σ)
        ((CON_1 ρ <= LAB_1 LAB_2 V_2 LAB_3 
                (@ (remember-contract V ((CON_0 ... -> CON_1) ρ))
                   (CON_0 ρ <= LAB_2 LAB_1 V_1 LAB_3 V_1) ... Λ))
         σ)
        blessed-β)
   
   ;; BLESSING
   (--> (((CON_1 ... -> any) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        (((CON_1 ... --> any) ρ <= LAB_1 LAB_2 V_1 LAB_3
                              (remember-contract V ((pred procedure? Λ) (env))))
         σ)
        (side-condition (term (∈ #t (δ procedure? V ★))))
        chk-fun-pass) 
   
   ;; DAMNING
   (--> (((CON_1 ... -> any) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((blame LAB_1 LAB_3 V_1 ((CON_1 ... -> any) (env)) V) σ)
        (side-condition (term (∈ #f (δ procedure? V ★))))
        chk-fun-fail-flat)))

(test
 (test/σ--> c ; (nat? <= 5)   -- provable
            (term ((pred exact-nonnegative-integer? f) 
                   (env) <= f g (-- (clos 0 (env))) f 
                   (-- (clos 5 (env)))))          
            (term (if (@ (-- (clos (flat-check ((pred exact-nonnegative-integer? f) (env)) 
                                               (-- (clos 5 (env))))
                                   (env)))
                         (-- (clos 5 (env))) 
                         Λ)
                      (remember-contract (-- (clos 5 (env))) 
                                         ((pred exact-nonnegative-integer? f) (env)))
                      (blame f f (-- (clos 0 (env))) 
                             ((pred exact-nonnegative-integer? f) (env))
                             (-- (clos 5 (env)))))))
 
 (test/σ--> c ; (prime? <= 5)   -- runable
            (term ((pred (prime? ^ h j) f) 
                   (env) <= f g (-- (clos 0 (env))) f 
                   (-- (clos 5 (env)))))
            (term (if (@ (-- (clos (flat-check ((pred (prime? ^ h j) f) (env))
                                               (-- (clos 5 (env))))
                                   (env)))
                         (-- (clos 5 (env))) 
                         Λ)
                      (remember-contract (-- (clos 5 (env))) 
                                         ((pred (prime? ^ h j) f) (env)))
                      (blame f f (-- (clos 0 (env))) 
                             ((pred (prime? ^ h j) f) (env))
                             (-- (clos 5 (env)))))))
 
 (test/σ--> c ; ((or/c prime? string?) <= 5)
            (term ((or/c (pred (prime? ^ f g) f) (pred string? f)) 
                   (env) <= f g (-- (clos 0 (env))) f 
                   (-- (clos 5 (env)))))
            (term (if (@ (-- (clos (flat-check ((or/c (pred (prime? ^ f g) f) 
                                                      (pred string? f)) 
                                                (env))
                                               (-- (clos 5 (env))))
                                   (env)))
                         (-- (clos 5 (env))) 
                         Λ)
                      (remember-contract (-- (clos 5 (env)) 
                                             ((pred (prime? ^ f g) f) (env))))
                      
                      (blame f f (-- (clos 0 (env)))
                             ((or/c (pred (prime? ^ f g) f) (pred string? f)) (env))
                             (-- (clos 5 (env))))))
            (term (if (@ (-- (clos (flat-check ((or/c (pred (prime? ^ f g) f) 
                                                      (pred string? f)) 
                                                (env))
                                               (-- (clos 5 (env))))
                                   (env)))
                         (-- (clos 5 (env))) 
                         Λ)
                      (remember-contract (-- (clos 5 (env)))
                                         ((pred string? f) (env)))
                      (blame f f (-- (clos 0 (env)))
                             ((or/c (pred (prime? ^ f g) f) (pred string? f)) (env))
                             (-- (clos 5 (env)))))))
 
 (test/σ--> c ; ((-> string?) <= 5)
            (term ((-> (pred string? †))
                   (env) <= f g (-- (clos 0 (env))) f 
                   (-- (clos 5 (env)))))
            (term (blame f f (-- (clos 0 (env))) 
                         ((-> (pred string? †)) (env))
                         (-- (clos 5 (env))))))
 
 (test/σ--> c ; ((or/c string? (-> string?)) <= (λ () "x")))
            (term ((or/c (pred string? f)
                         (-> (pred string? f)))
                   (env) <= f g (-- (clos 0 (env))) f 
                   (-- (clos (λ () "x") (env)))))
            
            (term (if (@ (-- (clos (flat-check ((pred string? f) (env))
                                               (-- (clos (λ () "x") (env))))
                                   (env)))
                         (-- (clos (λ () "x") (env)))
                         Λ)
                      (remember-contract (-- (clos (λ () "x") (env)))
                                         ((pred string? f) (env)))
                      ((-> (pred string? f)) 
                       (env) <= f g 
                       (-- (clos 0 (env))) f
                       (-- (clos (λ () "x") (env)))))))
 
 (test/σ--> c ; ((and/c (-> string?) (-> string?)) <= (λ () "x")))
            (term ((and/c (-> (pred string? f)) 
                          (-> (pred string? f)))
                   (env) <= f g (-- (clos 0 (env))) f 
                   (-- (clos (λ () "x") (env)))))
            (term ((-> (pred string? f)) 
                   (env) <= f g (-- (clos 0 (env))) f
                   ((-> (pred string? f)) 
                    (env) <= f g 
                    (-- (clos 0 (env))) f
                    (-- (clos (λ () "x") (env)))))))
 
 (test/σ--> c ; ((cons/c (-> string?) (-> string?)) <= (cons (λ () "x") (λ () "y")))
            (term ((cons/c (-> (pred string? f)) 
                           (-> (pred string? g)))
                   (env) <= f g (-- (clos 0 (env))) f
                   (-- (cons (-- (clos (λ () "x") (env)))
                             (-- (clos (λ () "y") (env)))))))
            (term (@ (-- (clos cons (env)))                     
                     ((-> (pred string? f)) 
                      (env) <= f g (-- (clos 0 (env))) f 
                      (-- (clos (λ () "x") (env))))                    
                     ((-> (pred string? g)) 
                      (env) <= f g (-- (clos 0 (env))) f 
                      (-- (clos (λ () "y") (env))))                      
                     Λ)))
 
 (test/σ--> c ; ((rec/c x (or/c string? (-> x)) <= "x")
          (term ((rec/c x (or/c (pred string? f) (-> x)))
                 (env) <= f g (-- (clos 0 (env))) f
                 (-- (clos "x" (env)))))
          (term ((or/c (pred string? f) 
                       (-> (rec/c x (or/c (pred string? f) (-> x)))))
                 (env) <= f g (-- (clos 0 (env))) f
                 (-- (clos "x" (env))))))
 
 (test/σ--> c ; ((cons/c (-> string?) (-> string?)) <= 3)
            (term ((cons/c (-> (pred string? f)) 
                           (-> (pred string? g)))
                   (env) <= f g (-- (clos 0 (env))) f
                   (-- (clos 3 (env)))))
            (term (blame f f (-- (clos 0 (env))) 
                         ((cons/c (-> (pred string? f)) 
                                  (-> (pred string? g))) 
                          (env)) 
                         (-- (clos 3 (env))))))
 
 (test--> c ; (@ ((string? --> (λ (x) (pred (λ (y) x)))) <= (λ (x) x)) "q")
          (term ((@ (((pred string? g) --> (λ (x) (pred (λ (y) x) f))) 
                     (env) <= f g (-- (clos 0 (env))) f 
                     (-- (clos (λ (x) x) (env))))
                     (-- (clos "q" (env)))
                     †)
                 (sto)))
          (redex-let 
           λcρ
           ([(ρ σ) (term (bind-vars (env) (sto) (x (-- (clos "q" (env))))))])
           (term (((pred (λ (y) x) f) ρ
                   <= f g (-- (clos 0 (env))) f 
                   (@ (-- (clos (λ (x) x) (env))
                          (((pred string? g) -> (λ (x) (pred (λ (y) x) f))) (env)))
                      ((pred string? g)
                       (env) <= g f (-- (clos "q" (env))) f
                       (-- (clos "q" (env))))
                      Λ))
                  σ)))) 
 (test/σ--> c ; (@ ((string? --> string?) <= (λ () "x")))
            (term (@ (((pred string? g) --> (pred string? f)) 
                      (env) <= f g (-- (clos 0 (env))) f (-- (clos (λ (x) x) (env))))
                     (-- (clos "x" (env)))
                     †))
            (term ((pred string? f) 
                   (env) <= f g (-- (clos 0 (env))) f 
                   (@ (-- (clos (λ (x) x) (env))
                          (((pred string? g) -> (pred string? f)) (env)))
                      ((pred string? g)
                       (env) <= g f (-- (clos "x" (env))) f
                       (-- (clos "x" (env))))
                      Λ))))
 
 (test/σ--> c ; ((-> string) <= (λ () 1))
            (term ((-> (pred string? f)) 
                   (env) <= f g (-- (clos 0 (env))) f
                   (-- (clos (λ () 1) (env)))))
            (term ((--> (pred string? f))
                   (env) <= f g (-- (clos 0 (env))) f
                   (-- (clos (λ () 1) (env)))))))
