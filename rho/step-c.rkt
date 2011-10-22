#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "flat-check.rkt" "util.rkt")
(provide c)
(test-suite test step-c)

(define c
  (reduction-relation
   λcρ #:domain D
   
   ;; FLAT CONTRACTS   
   (--> (FLAT ρ <= LAB_1 LAB_2 V_1 LAB_3 V)  ; FIXME: first V_1 was V-or-AE
        (if (@ (flat-check (FLAT ρ) V) V Λ)
            (remember-contract V (FLAT ρ))
            (blame LAB_1 LAB_3 V_1 (FLAT ρ) V))
        flat-check)   
   
   ;; HIGHER-ORDER CONTRACTS   
   (--> ((or/c FLAT HOC) ρ <= LAB_1 LAB_2 V_1 LAB_3 V)
        (if (@ (flat-check (FLAT ρ) V) V Λ)
            (remember-contract V (FLAT ρ))
            (HOC ρ <= LAB_1 LAB_2 V_1 LAB_3 V))
        or/c-hoc)
   
   (--> ((and/c CON_0 CON_1) ρ <= LAB_1 LAB_2 V_1 LAB_3 V)
        (CON_1 ρ <= LAB_1 LAB_2 V_1 LAB_3 
             (CON_0 ρ <= LAB_1 LAB_2 V_1 LAB_3 V))
        (where HOC (and/c CON_0 CON_1))
        and/c-hoc)
   
   (--> ((rec/c X CON) ρ <= LAB_1 LAB_2 V_1 LAB_3 V)
        ((unroll HOC) ρ <= LAB_1 LAB_2 V_1 LAB_3 V)
        (where HOC (rec/c X CON))
        unroll-HOC)
   
   ;; PAIR CONTRACTS
   ;; FIXME: forgets what's known about the pair.   
   (--> ((cons/c CON_0 CON_1) ρ <= LAB_1 LAB_2 V_1 LAB_3 V)
        (@ (-- (clos cons ()))
           (CON_0 ρ <= LAB_1 LAB_2 V_1 LAB_3 
                  (@ (-- (clos car ()))
                     (remember-contract V ((pred cons? Λ) ())) Λ))
           (CON_1 ρ <= LAB_1 LAB_2 V_1 LAB_3 
                  (@ (-- (clos cdr ()))
                     (remember-contract V ((pred cons? Λ) ())) Λ))
           Λ)
        (where HOC (cons/c CON_0 CON_1))
        (where #t (∈ #t (δ cons? V Λ)))
        check-cons-pass)
   
   (--> ((cons/c CON_0 CON_1) ρ <= LAB_1 LAB_2 V_1 LAB_3 V)
        (blame LAB_1 LAB_3 V_1 (HOC ρ) V)
        (where HOC (cons/c CON_0 CON_1))
        (where #t (∈ #f (δ cons? V Λ)))
        check-cons-fail)
   
   ;; PROCEDURE CONTRACTS      
   (--> (@ ((CON_0 ..._1 --> (λ (X ..._1) CON_1)) ρ <= LAB_1 LAB_2 V_2 LAB_3 V) V_1 ..._1 LAB)        
        (CON_1 (env-extend ρ (X V_1) ...) ; indy
               <= LAB_1 LAB_2 V_2 LAB_3 
               (@ (remember-contract V ((CON_a0 ... -> CON_a1) ()) )
                  (CON_0 ρ <= LAB_2 LAB_1 V_1 LAB_3 V_1) ... Λ))
        (where (CON_a0 ... CON_a1) 
               ,(map (λ _ (term (pred (λ (x) #t) Λ))) 
                     (term (CON_0 ... CON_1))))
        blessed-β-dep)
   
   (--> (@ ((CON_0 ..._1 --> CON_1) ρ <= LAB_1 LAB_2 V_2 LAB_3 V) V_1 ..._1 LAB)        
        (CON_1 ρ <= LAB_1 LAB_2 V_2 LAB_3 
             (@ (remember-contract V ((CON_a0 ... -> CON_a1) ()))
                (CON_0 ρ <= LAB_2 LAB_1 V_1 LAB_3 V_1) ... Λ))
        (where (CON_a0 ... CON_a1)
               ,(map (λ _ (term (pred (λ (x) #t) Λ))) 
                     (term (CON_0 ... CON_1))))
        blessed-β)
   
   ;; BLESSING
   (--> ((CON_1 ... -> any) ρ <= LAB_1 LAB_2 V_1 LAB_3 V)
        ((CON_1 ... --> any) ρ <= LAB_1 LAB_2 V_1 LAB_3
                             (remember-contract V ((pred procedure? Λ) ())))
        (side-condition (term (∈ #t (δ procedure? V ★))))
        chk-fun-pass) 
   
   ;; DAMNING
   (--> ((CON_1 ... -> any) ρ <= LAB_1 LAB_2 V_1 LAB_3 V)
        (blame LAB_1 LAB_3 V_1 ((CON_1 ... -> any) ()) V)
        (side-condition (term (∈ #f (δ procedure? V ★))))
        chk-fun-fail-flat)))

(test
 (test--> c ; (nat? <= 5)   -- provable
          (term ((pred exact-nonnegative-integer? f) 
                 () <= f g (-- (clos 0 ())) f 
                 (-- (clos 5 ()))))
          (term (if (@ (-- (clos (λ (x) #t) ())) 
                       (-- (clos 5 ())) 
                       Λ)
                    (remember-contract (-- (clos 5 ())) 
                                       ((pred exact-nonnegative-integer? f) ()))
                    (blame f f (-- (clos 0 ())) 
                           ((pred exact-nonnegative-integer? f) ())
                           (-- (clos 5 ()))))))
 
 (test--> c ; (prime? <= 5)   -- runable
          (term ((pred (prime? ^ h j) f) 
                 () <= f g (-- (clos 0 ())) f 
                 (-- (clos 5 ()))))
          (term (if (@ (-- (clos (λ (x) (@ (prime? ^ h j) x f)) ())) 
                       (-- (clos 5 ())) 
                       Λ)
                    (remember-contract (-- (clos 5 ())) 
                                       ((pred exact-nonnegative-integer? f) ()))
                    (blame f f (-- (clos 0 ())) 
                           ((pred (prime? ^ h j) f) ())
                           (-- (clos 5 ()))))))
 
  (test--> c ; ((or/c prime? string?) <= 5)
          (term ((or/c (pred (prime? ^ f g) f) (pred string? f)) 
                 () <= f g (-- (clos 0 ())) f 
                 (-- (clos 5 ()))))
          (term (if (@ (flat-check ((or/c (pred (prime? ^ f g) f) 
                                          (pred string? f)) 
                                    ())
                                   (-- (clos 5 ()))) 
                       (-- (clos 5 ())) 
                       Λ)
                    (-- (clos 5 ()) 
                        ;; FIXME: why isn't this contract remembered?
                        #;((or/c (pred (prime? ^ f g) f) (pred string? f)) ()))
                    (blame f f (-- (clos 0 ()))
                           ((or/c (pred (prime? ^ f g) f) (pred string? f)) ())
                           (-- (clos 5 ()))))))
   
 (test--> c ; ((-> string?) <= 5)
          (term ((-> (pred string? †))
                 () <= f g (-- (clos 0 ())) f 
                 (-- (clos 5 ()))))
          (term (blame f f (-- (clos 0 ())) 
                       ((-> (pred string? †)) ())
                       (-- (clos 5 ())))))
 
 (test--> c ; ((or/c string? (-> string?)) <= (λ () "x")))
          (term ((or/c (pred string? f)
                       (-> (pred string? f)))
                 () <= f g (-- (clos 0 ())) f 
                 (-- (clos (λ () "x") ()))))
          
          (term (if (@ (flat-check ((pred string? f) ())
                                   (-- (clos (λ () "x") ())))
                       (-- (clos (λ () "x") ()))
                       Λ)
                    (remember-contract (-- (clos (λ () "x") ()))
                                       ((pred string? f) ()))
                    ((-> (pred string? f)) 
                     () <= f g 
                     (-- (clos 0 ())) f
                     (-- (clos (λ () "x") ()))))))
 
 (test--> c ; ((and/c (-> string?) (-> string?)) <= (λ () "x")))
           (term ((and/c (-> (pred string? f)) 
                         (-> (pred string? f)))
                  () <= f g (-- (clos 0 ())) f 
                  (-- (clos (λ () "x") ()))))
           (term ((-> (pred string? f)) 
                  () <= f g (-- (clos 0 ())) f
                  ((-> (pred string? f)) 
                   () <= f g 
                   (-- (clos 0 ())) f
                   (-- (clos (λ () "x") ()))))))
 
 (test--> c ; ((rec/c x (or/c string? (-> x)) <= "x")
          (term ((rec/c x (or/c (pred string? f) (-> x)))
                 () <= f g (-- (clos 0 ())) f
                 (-- (clos "x" ()))))
          (term ((or/c (pred string? f) 
                       (-> (rec/c x (or/c (pred string? f) (-> x)))))
                 () <= f g (-- (clos 0 ())) f
                 (-- (clos "x" ())))))
 
 (test--> c ; ((cons/c (-> string?) (-> string?)) <= (cons (λ () "x") (λ () "y")))
          (term ((cons/c (-> (pred string? f)) 
                         (-> (pred string? g)))
                 () <= f g (-- (clos 0 ())) f
                 (-- (cons (-- (clos (λ () "x") ()))
                           (-- (clos (λ () "y") ()))))))
          (term (@ (-- (clos cons ()))
                   ((-> (pred string? f)) 
                    () <= f g (-- (clos 0 ())) f 
                    (@ (-- (clos car ())) 
                       (-- (cons (-- (clos (λ () "x") ())) 
                                 (-- (clos (λ () "y") ())))) 
                       Λ))
                   ((-> (pred string? g)) 
                    () <= f g (-- (clos 0 ())) f 
                    (@ (-- (clos cdr ())) 
                       (-- (cons (-- (clos (λ () "x") ())) 
                                 (-- (clos (λ () "y") ())))) 
                       Λ))
                   Λ)))
 
 (test--> c ; ((cons/c (-> string?) (-> string?)) <= 3)
          (term ((cons/c (-> (pred string? f)) 
                         (-> (pred string? g)))
                 () <= f g (-- (clos 0 ())) f
                 (-- (clos 3 ()))))
          (term (blame f f (-- (clos 0 ())) 
                       ((cons/c (-> (pred string? f)) 
                                (-> (pred string? g))) 
                        ()) 
                       (-- (clos 3 ())))))
          
 (test--> c ; (@ ((string? --> (λ (x) (pred (λ (y) x)))) <= (λ (x) x)) "q")
          (term (@ (((pred string? g) --> (λ (x) (pred (λ (y) x) f))) 
                    () <= f g (-- (clos 0 ())) f 
                    (-- (clos (λ (x) x) ())))
                   (-- (clos "q" ()))
                   †))
          (term ((pred (λ (y) x) f)
                 ((x (-- (clos "q" ()))))
                 <= f g (-- (clos 0 ())) f 
                 (@ (-- (clos (λ (x) x) ()))
                    ((pred string? g)
                     () <= g f (-- (clos "q" ())) f
                     (-- (clos "q" ())))
                    Λ))))
  
 (test--> c ; (@ ((string? --> string?) <= (λ () "x")))
          (term (@ (((pred string? g) --> (pred string? f)) 
                    () <= f g (-- (clos 0 ())) f (-- (clos (λ (x) x) ())))
                   (-- (clos "x" ()))
                   †))
          (term ((pred string? f) 
                 () <= f g (-- (clos 0 ())) f 
                 (@ (-- (clos (λ (x) x) ()))
                    ((pred string? g)
                     () <= g f (-- (clos "x" ())) f
                     (-- (clos "x" ())))
                    Λ))))
 
 (test--> c ; ((-> string) <= (λ () 1))
          (term ((-> (pred string? f)) 
                 () <= f g (-- (clos 0 ())) f
                 (-- (clos (λ () 1) ()))))
          (term ((--> (pred string? f))
                 () <= f g (-- (clos 0 ())) f
                 (-- (clos (λ () 1) ()))))))
