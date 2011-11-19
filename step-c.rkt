#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "check.rkt" "util.rkt")
(provide c)
(test-suite test step-c)

(define c
  (reduction-relation
   λcρ #:domain (D σ)
      
   (--> ((ANYCON ρ <= LAB_1 LAB_2 V_1 LAB_3 D) σ)
        (D σ)
        any/c-drop)
   
   ;; FLAT CONTRACTS   
   (--> ((FLAT ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)  ; FIXME: first V_1 was V-or-AE
        ((if (@ (-- (↓ (flat-check (FLAT ρ) V) ρ)) V Λ)
             V_2
             (blame LAB_1 LAB_3 V_1 (FLAT ρ) V))
         σ)
        (where V_2 (remember-contract V (FLAT ρ)))
        (side-condition (not (redex-match λcρ ANYCON (term FLAT))))
        flat-check)
   
   ;; HIGHER-ORDER CONTRACTS   
   (--> (((or/c FLAT HOC) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((if (@ (-- (↓ (flat-check (FLAT ρ) V) (env))) V Λ)
             V_2
             (HOC ρ <= LAB_1 LAB_2 V_1 LAB_3 V))
         σ)
        (where V_2 (remember-contract V (FLAT ρ)))
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
        ((@ (-- (↓ cons (env)))
            (CON_0 ρ <= LAB_1 LAB_2 V_1 LAB_3 V_car)
            (CON_1 ρ <= LAB_1 LAB_2 V_1 LAB_3 V_cdr)
            Λ)
         σ)
        (where HOC (cons/c CON_0 CON_1))
        (where #t (∈ #t (δ cons? V)))
        (where (any_0 ... V_car any_1 ...) (δ car V))
        (where (any_2 ... V_cdr any_3 ...) (δ cdr V))
        check-cons-pass)
   
   (--> (((cons/c CON_0 CON_1) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((blame LAB_1 LAB_3 V_1 (HOC ρ) V) σ)
        (where HOC (cons/c CON_0 CON_1))
        (where #t (∈ #f (δ cons? V)))
        check-cons-fail)
   
   ;; STRUCT CONTRACTS
   ;; FIXME: forgets what's known about the struct.   
   (--> (((struct/c X_m X_tag CON ...) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((@ (-- (↓ (s-cons X_m X_tag ,(length (term (CON ...)))) (env)))
            (CON ρ <= LAB_1 LAB_2 V_r LAB_3 V_1) ...
            Λ)
         σ)
        (where HOC (struct/c X_m X_tag CON ...))
        (where #t (∈ #t (δ (s-pred X_m X_tag) V)))
        (where (natural_1 ...) ,(for/list ([i (length (term (CON ...)))]) i))
        (where ((any_0 ... V_r any_1 ...) ...) ((δ (s-ref X_m X_tag natural_1) V) ...))
        check-struct-pass)
   
   (--> (((struct/c X_m X_tag CON ...) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((blame LAB_1 LAB_3 V_1 (HOC ρ) V) σ)
        (where HOC (struct/c X_m X_tag CON ...))
        (where #t (∈ #f (δ (s-pred X_m X_tag) V)))
        check-struct-fail)
   
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
   
   (--> ((@ ((CON_0 ..._1 CON_r -->* CON_1) ρ <= LAB_1 LAB_2 V_2 LAB_3 V) V_1 ..._1 V_r ... LAB) σ)
        ((CON_1 ρ <= LAB_1 LAB_2 V_2 LAB_3 
                (@* (remember-contract V ((CON_0 ... CON_r ->* CON_1) ρ))
                    (CON_0 ρ <= LAB_2 LAB_1 V_1 LAB_3 V_1) 
                    ... 
                    (CON_r ρ <= LAB_2 LAB_1 V_ls LAB_3 V_ls)  ;; This isn't right -- double turning into a list.
                    Λ))
         σ)
        (where V_ls (list->list-value (V_r ...)))
        blessed-β*)
   
   (--> ((@* V_1 ... V_r LAB) σ)
        ((@ V_1 ... V ... LAB) σ)
        (where (V ...) (list-value->list V_r))
        @*)
   
   ;; BLESSING
   (--> ((CARROW ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        (((bless CARROW) ρ <= LAB_1 LAB_2 V_1 LAB_3
                         (remember-contract V ((pred procedure? Λ) (env))))
         σ)
        (side-condition (term (∈ #t (δ procedure? V))))
        chk-fun-pass) 
   
   ;; DAMNING
   (--> (((CON_1 ... -> any) ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ)
        ((blame LAB_1 LAB_3 V_1 ((CON_1 ... -> any) (env)) V) σ)
        (side-condition (term (∈ #f (δ procedure? V))))
        chk-fun-fail-flat)))


(define-metafunction λcρ
  bless : CARROW -> BARROW
  [(bless (CON_1 ... -> any)) (CON_1 ... --> any)]
  [(bless (CON_1 ... ->* any)) (CON_1 ... -->* any)])

(test
 (test/σ--> c ; (nat? <= 5)   -- provable
            (term ((pred exact-nonnegative-integer? f) 
                   (env) <= f g (-- (↓ 0 (env))) f 
                   (-- (↓ 5 (env)))))          
            (term (if (@ (-- (↓ (flat-check ((pred exact-nonnegative-integer? f) (env)) 
                                               (-- (↓ 5 (env))))
                                   (env)))
                         (-- (↓ 5 (env))) 
                         Λ)
                      (remember-contract (-- (↓ 5 (env))) 
                                         ((pred exact-nonnegative-integer? f) (env)))
                      (blame f f (-- (↓ 0 (env))) 
                             ((pred exact-nonnegative-integer? f) (env))
                             (-- (↓ 5 (env)))))))
 
 (test/σ--> c ; (prime? <= 5)   -- runable
            (term ((pred (prime? ^ h j) f) 
                   (env) <= f g (-- (↓ 0 (env))) f 
                   (-- (↓ 5 (env)))))
            (term (if (@ (-- (↓ (flat-check ((pred (prime? ^ h j) f) (env))
                                               (-- (↓ 5 (env))))
                                   (env)))
                         (-- (↓ 5 (env))) 
                         Λ)
                      (remember-contract (-- (↓ 5 (env))) 
                                         ((pred (prime? ^ h j) f) (env)))
                      (blame f f (-- (↓ 0 (env))) 
                             ((pred (prime? ^ h j) f) (env))
                             (-- (↓ 5 (env)))))))
 
 (test/σ--> c ; ((or/c prime? string?) <= 5)
            (term ((or/c (pred (prime? ^ f g) f) (pred string? f)) 
                   (env) <= f g (-- (↓ 0 (env))) f 
                   (-- (↓ 5 (env)))))
            (term (if (@ (-- (↓ (flat-check ((or/c (pred (prime? ^ f g) f) 
                                                      (pred string? f)) 
                                                (env))
                                               (-- (↓ 5 (env))))
                                   (env)))
                         (-- (↓ 5 (env))) 
                         Λ)
                      (remember-contract (-- (↓ 5 (env)) 
                                             ((pred (prime? ^ f g) f) (env))))
                      
                      (blame f f (-- (↓ 0 (env)))
                             ((or/c (pred (prime? ^ f g) f) (pred string? f)) (env))
                             (-- (↓ 5 (env))))))
            (term (if (@ (-- (↓ (flat-check ((or/c (pred (prime? ^ f g) f) 
                                                      (pred string? f)) 
                                                (env))
                                               (-- (↓ 5 (env))))
                                   (env)))
                         (-- (↓ 5 (env))) 
                         Λ)
                      (remember-contract (-- (↓ 5 (env)))
                                         ((pred string? f) (env)))
                      (blame f f (-- (↓ 0 (env)))
                             ((or/c (pred (prime? ^ f g) f) (pred string? f)) (env))
                             (-- (↓ 5 (env)))))))
 
 (test/σ--> c ; ((-> string?) <= 5)
            (term ((-> (pred string? †))
                   (env) <= f g (-- (↓ 0 (env))) f 
                   (-- (↓ 5 (env)))))
            (term (blame f f (-- (↓ 0 (env))) 
                         ((-> (pred string? †)) (env))
                         (-- (↓ 5 (env))))))
 
 (test/σ--> c ; ((or/c string? (-> string?)) <= (λ () "x")))
            (term ((or/c (pred string? f)
                         (-> (pred string? f)))
                   (env) <= f g (-- (↓ 0 (env))) f 
                   (-- (↓ (λ () "x") (env)))))
            
            (term (if (@ (-- (↓ (flat-check ((pred string? f) (env))
                                               (-- (↓ (λ () "x") (env))))
                                   (env)))
                         (-- (↓ (λ () "x") (env)))
                         Λ)
                      (remember-contract (-- (↓ (λ () "x") (env)))
                                         ((pred string? f) (env)))
                      ((-> (pred string? f)) 
                       (env) <= f g 
                       (-- (↓ 0 (env))) f
                       (-- (↓ (λ () "x") (env)))))))
 
 (test/σ--> c ; ((and/c (-> string?) (-> string?)) <= (λ () "x")))
            (term ((and/c (-> (pred string? f)) 
                          (-> (pred string? f)))
                   (env) <= f g (-- (↓ 0 (env))) f 
                   (-- (↓ (λ () "x") (env)))))
            (term ((-> (pred string? f)) 
                   (env) <= f g (-- (↓ 0 (env))) f
                   ((-> (pred string? f)) 
                    (env) <= f g 
                    (-- (↓ 0 (env))) f
                    (-- (↓ (λ () "x") (env)))))))
 
 (test/σ--> c ; ((cons/c (-> string?) (-> string?)) <= (cons (λ () "x") (λ () "y")))
            (term ((cons/c (-> (pred string? f)) 
                           (-> (pred string? g)))
                   (env) <= f g (-- (↓ 0 (env))) f
                   (-- (cons (-- (↓ (λ () "x") (env)))
                             (-- (↓ (λ () "y") (env)))))))
            (term (@ (-- (↓ cons (env)))                     
                     ((-> (pred string? f)) 
                      (env) <= f g (-- (↓ 0 (env))) f 
                      (-- (↓ (λ () "x") (env))))                    
                     ((-> (pred string? g)) 
                      (env) <= f g (-- (↓ 0 (env))) f 
                      (-- (↓ (λ () "y") (env))))                      
                     Λ)))
 
 (test/σ--> c ; ((rec/c x (or/c string? (-> x)) <= "x")
          (term ((rec/c x (or/c (pred string? f) (-> x)))
                 (env) <= f g (-- (↓ 0 (env))) f
                 (-- (↓ "x" (env)))))
          (term ((or/c (pred string? f) 
                       (-> (rec/c x (or/c (pred string? f) (-> x)))))
                 (env) <= f g (-- (↓ 0 (env))) f
                 (-- (↓ "x" (env))))))
 
 (test/σ--> c ; ((cons/c (-> string?) (-> string?)) <= 3)
            (term ((cons/c (-> (pred string? f)) 
                           (-> (pred string? g)))
                   (env) <= f g (-- (↓ 0 (env))) f
                   (-- (↓ 3 (env)))))
            (term (blame f f (-- (↓ 0 (env))) 
                         ((cons/c (-> (pred string? f)) 
                                  (-> (pred string? g))) 
                          (env)) 
                         (-- (↓ 3 (env))))))
 
 (test--> c ; (@ ((string? --> (λ (x) (pred (λ (y) x)))) <= (λ (x) x)) "q")
          (term ((@ (((pred string? g) --> (λ (x) (pred (λ (y) x) f))) 
                     (env) <= f g (-- (↓ 0 (env))) f 
                     (-- (↓ (λ (x) x) (env))))
                     (-- (↓ "q" (env)))
                     †)
                 (sto)))
          (redex-let 
           λcρ
           ([(ρ σ) (term (bind-vars (env) (sto) (x (-- (↓ "q" (env))))))])
           (term (((pred (λ (y) x) f) ρ
                   <= f g (-- (↓ 0 (env))) f 
                   (@ (-- (↓ (λ (x) x) (env))
                          (((pred string? g) -> (λ (x) (pred (λ (y) x) f))) (env)))
                      ((pred string? g)
                       (env) <= g f (-- (↓ "q" (env))) f
                       (-- (↓ "q" (env))))
                      Λ))
                  σ)))) 
 (test/σ--> c ; (@ ((string? --> string?) <= (λ () "x")))
            (term (@ (((pred string? g) --> (pred string? f)) 
                      (env) <= f g (-- (↓ 0 (env))) f (-- (↓ (λ (x) x) (env))))
                     (-- (↓ "x" (env)))
                     †))
            (term ((pred string? f) 
                   (env) <= f g (-- (↓ 0 (env))) f 
                   (@ (-- (↓ (λ (x) x) (env))
                          (((pred string? g) -> (pred string? f)) (env)))
                      ((pred string? g)
                       (env) <= g f (-- (↓ "x" (env))) f
                       (-- (↓ "x" (env))))
                      Λ))))
 
 (test/σ--> c ; ((-> string) <= (λ () 1))
            (term ((-> (pred string? f)) 
                   (env) <= f g (-- (↓ 0 (env))) f
                   (-- (↓ (λ () 1) (env)))))
            (term ((--> (pred string? f))
                   (env) <= f g (-- (↓ 0 (env))) f
                   (-- (↓ (λ () 1) (env)))))))
