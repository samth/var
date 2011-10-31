#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test check)

(define-metafunction λcρ
  flat-check : (FLAT ρ) V -> D
  [(flat-check (FLAT ρ) V)
   (fc/c X () FLAT ρ V)
   ;; FIXME generating syntax.  Is there any possibility of capture here?  Don't think so
   (where X ,(variable-not-in (term (FLAT V)) 'x))])
 
(define-metafunction λcρ
  fc/c : X ((C V) ...) FLAT ρ V -> D
  [(fc/c X (any_1 ... (C V) any_2 ...) FLAT ρ V) 
   (-- (clos (λ (X) #t) (env)))
   (where #t (≡C C (FLAT ρ)))]                                          
  ;; Why did we bother with something like this?
  ;;[(fc/c X any anyc V) (λ (x) #t)]  
  [(fc/c X any FLAT ρ V)
   (-- (clos (λ (X) #t) (env)))
   (where #t (contract-in (FLAT ρ) V))]
  [(fc/c X any FLAT ρ V)
   (-- (clos (λ (X) #f) (env)))
   (where #t (contract-not-in (FLAT ρ) V))]  
  [(fc/c X any (and/c FLAT_1 FLAT_2) ρ V)
   (-- (clos (λ (X) (if (@ f1 X Λ) (@ f2 X Λ) #f))
             (env (f1 (fc/c X any FLAT_1 ρ V))
                  (f2 (fc/c X any FLAT_2 ρ V)))))]
  [(fc/c X any (not/c FLAT_1) ρ V)
   (-- (clos (λ (X) (if (@ f1 X Λ) #f #t))
             (env (f1 (fc/c X any FLAT_1 ρ V)))))]
  [(fc/c X any (cons/c FLAT_1 FLAT_2) ρ
         (-- (cons V_1 V_2) C ...))
   (-- (clos (λ (X) (if (@ f1 (@ car X Λ) Λ) (@ f2 (@ cdr X Λ) Λ) #f))
             (env (f1 (fc/c X any FLAT_1 ρ V_1))
                  (f2 (fc/c X any FLAT_2 ρ V_2)))))]
  [(fc/c X any (pred PREDV LAB) ρ V)
   ;; η-expansion for right blame label in case PREDV is not a predicate.
   (-- (clos (λ (X) (@ PREDV X LAB)) ρ))]
  [(fc/c X any (or/c FLAT_1 FLAT_2) ρ V)
   (-- (clos (λ (X) (if (@ f1 X Λ) #t (@ f2 X Λ)))
             (env (f1 (fc/c X any FLAT_1 ρ V))
                  (f2 (fc/c X any FLAT_2 ρ V)))))]
  [(fc/c X_1 any (rec/c X CON) ρ V)   
   (fc/c X_1 ((((rec/c X CON) ρ) V) . any) (unroll (rec/c X CON)) ρ V)]    
  [(fc/c X any (cons/c CON_1 CON_2) ρ AV)
   (-- (clos (λ (X) (amb/e *black-hole* (@ X_n X Λ) ...)) 
             (env (*black-hole* (join-contracts))
                  (X_n V_r) ...)))
   (where (V_r ...)
          ,(remove-duplicates
            (for*/list ([l (term (proj-left AV))]
                        [r (term (proj-right AV))])
              (term (-- (clos (λ (x)
                                (if (@ f1 (@ car x Λ) Λ)
                                    (@ f2 (@ cdr x Λ) Λ)
                                    #f))
                              (env (f1 (fc/c X any CON_1 ρ ,l))
                                   (f2 (fc/c X any CON_2 ρ ,r)))))))))
   (where (X_n ...) ,(gen-xs (term (V_r ...))))
   (where #t (proves AV cons?))]
  [(fc/c X any (cons/c CON_1 CON_2) ρ AV)
   (-- (clos (λ (X)
               (amb/e *black-hole*
                      #f
                      (if (@ f1 *black-hole* Λ)
                          (@ f2 *black-hole* Λ)
                          #f)))
             (env (f1 (fc/c X any CON_1 ρ (join-contracts)))
                  (f2 (fc/c X any CON_2 ρ (join-contracts)))
                  (*black-hole* (join-contracts)))))
   ;; using *black-hole* instead of (car X) and (cdr X) avoids spurious blame of the language
   ;; (proj-{left,right} AV) can't produce anything interesting here, 
   ;; b/c then either AV is an or/c (impossible), or AV is a cons/c (also impossible)
   (where #f (proves AV cons?))
   (where #f (refutes AV cons?))])


(test 
 (test-equal 
  (term (flat-check ((pred exact-nonnegative-integer? f) (env)) (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) #t) (env)))))
 (test-equal
  (term (flat-check ((pred exact-nonnegative-integer? f) (env)) (-- (clos "x" (env)))))
  (term (-- (clos (λ (x) #f) (env)))))
 (test-equal
  (term (flat-check ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) (@ (prime? ^ f g) x f)) (env)))))
 (test-equal
  (term (flat-check ((not/c (pred (prime? ^ f g) f)) (env)) (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) (if (@ f1 x Λ) #f #t)) 
                  (env [f1 (flat-check ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env))))])))))
 (test-equal
  (term (flat-check ((and/c (pred (prime? ^ f g) f)
                            (pred (composite? ^ f g) f)) 
                     (env)) 
                    (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) (if (@ f1 x Λ) (@ f2 x Λ) #f))
                  (env (f1 (flat-check ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env)))))
                       (f2 (flat-check ((pred (composite? ^ f g) f) (env)) (-- (clos 0 (env))))))))))
 (test-equal 
  (term (flat-check ((or/c (pred (prime? ^ f g) f)
                           (pred (composite? ^ f g) f)) 
                     (env)) 
                    (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) (if (@ f1 x Λ) #t (@ f2 x Λ)))
                  (env (f1 (flat-check ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env)))))
                       (f2 (flat-check ((pred (composite? ^ f g) f) (env)) (-- (clos 0 (env))))))))))
 (test-equal 
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- (cons (-- (clos 0 (env))) (-- (clos 1 (env)))))))
  (term 
   (-- (clos (λ (x) (if (@ f1 (@ car x Λ) Λ) (@ f2 (@ cdr x Λ) Λ) #f))
                  (env (f1 (flat-check ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env)))))
                       (f2 (flat-check ((pred (composite? ^ f g) f) (env)) (-- (clos 1 (env))))))))))
 (test-equal
  (term (flat-check ((rec/c z (pred (prime? ^ f g) f)) (env)) (-- (clos 0 (env)))))
  (term (flat-check ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env))))))
 
 (test-equal
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- ((pred cons? f) (env)))))
  (term (-- (clos (λ (x) (@ x0 x Λ))
                  (env (*black-hole* (join-contracts))
                       (x0 (-- (clos (λ (x) (if (@ f1 (@ car x Λ) Λ) (@ f2 (@ cdr x Λ) Λ) #f))
                                (env (f1 (-- (clos (λ (x) (@ (prime? ^ f g) x f)) (env))))
                                     (f2 (-- (clos (λ (x) (@ (composite? ^ f g) x f)) (env)))))))))))))
 
 (test-equal 
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- ((∧) (env)))))
  (term (-- (clos (λ (x1)
                    (amb/e *black-hole* 
                           #f
                           (if (@ f1 *black-hole* Λ)
                               (@ f2 *black-hole* Λ)
                               #f)))
                  (env (f1 (flat-check ((pred (prime? ^ f g) f) (env)) (join-contracts)))
                       (f2 (flat-check ((pred (composite? ^ f g) f) (env)) (join-contracts)))
                       (*black-hole* (join-contracts)))))))
 (test-equal
  (term (flat-check ((rec/c x (or/c (pred empty? †)
                                    (cons/c (pred zero? †) x)))
                     (env))
                    (-- ((∧) (env)))))
  (term (-- (clos (λ (x1)
                    (if (@ f1 x1 Λ)
                        #t
                        (@ f2 x1 Λ)))                                          
                  (env (f1 (flat-check ((pred empty? †) (env)) (join-contracts)))
                       (f2 (-- (clos (λ (x1) (amb/e *black-hole*
                                                    #f 
                                                    (if (@ f1 *black-hole* Λ)
                                                        (@ f2 *black-hole* Λ)
                                                        #f)))
                                     (env (f1 (flat-check ((pred zero? †) (env)) (join-contracts)))
                                          (f2 (-- (clos (λ (x1) #t) (env))))
                                          (*black-hole* (join-contracts))))))))))))
