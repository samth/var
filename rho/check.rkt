#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test check)

(define-metafunction λcρ
  flat-check : (FLAT ρ) V -> D  
  [(flat-check (FLAT ρ) V)
   (-- (clos (fc/e (FLAT ρ) V)
             (env (*black-hole* (-- ((∧) (env)))))))])
 
(define-metafunction λcρ
  fc/e : (FLAT ρ) V -> EXP
  [(fc/e (FLAT ρ) V)
   (fc/c X () FLAT ρ V)
   ;; FIXME generating syntax.  Is there any possibility of capture here?  Don't think so
   (where X ,(variable-not-in (term (FLAT V)) 'x))])

(define-metafunction λcρ
  fc/c : X ((C V) ...) FLAT ρ V -> EXP
  [(fc/c X (any_1 ... (C V) any_2 ...) FLAT ρ V) 
   (λ (X) #t)
   (where #t (≡C C (FLAT ρ)))]                                          
  ;; Why did we bother with something like this?
  ;;[(fc/c X any anyc V) (λ (x) #t)]  
  [(fc/c X any FLAT ρ V)
   (λ (X) #t)
   (where #t (contract-in (FLAT ρ) V))]
  [(fc/c X any FLAT ρ V)
   (λ (X) #f)
   (where #t (contract-not-in (FLAT ρ) V))]  
  [(fc/c X any (and/c FLAT_1 FLAT_2) ρ V)
   (λ (X) (if (@ EXP_1 X Λ) (@ EXP_2 X Λ) #f))
   (where EXP_1 (fc/c X any FLAT_1 ρ V))
   (where EXP_2 (fc/c X any FLAT_2 ρ V))]
  [(fc/c X any (not/c FLAT_1) ρ V)
   (λ (X) (if (@ EXP X Λ) #f #t))
   (where EXP (fc/c X any FLAT_1 ρ V))]
  [(fc/c X any (cons/c FLAT_1 FLAT_2) ρ (-- (cons V_1 V_2) C ...))
   (λ (X) (if (@ EXP_1 (@ car X Λ) Λ) (@ EXP_2 (@ cdr X Λ) Λ) #f))
   (where EXP_1 (fc/c X any FLAT_1 ρ V_1))
   (where EXP_2 (fc/c X any FLAT_2 ρ V_2))]
  [(fc/c X any (pred PREDV LAB) ρ V)
   ;; η-expansion for right blame label in case PREDV is not a predicate.
   (λ (X) (@ PREDV X LAB))]
  [(fc/c X any (or/c FLAT_1 FLAT_2) ρ V)
   (λ (X) (if (@ EXP_1 X Λ) #t (@ EXP_2 X Λ)))
   (where EXP_1 (fc/c X any FLAT_1 ρ V))
   (where EXP_2 (fc/c X any FLAT_2 ρ V))]
  [(fc/c X_1 any (rec/c X CON) ρ V)   
   (fc/c X_1 ((((rec/c X CON) ρ) V) . any) (unroll (rec/c X CON)) ρ V)]
  [(fc/c X any (cons/c CON_1 CON_2) ρ AV)
   (λ (X) (amb/e *black-hole* (@ EXP_n X Λ) ...))                     
   (where (EXP_n ...)
          ,(remove-duplicates
            (for*/list ([l (term (proj-left AV))]
                        [r (term (proj-right AV))])
              (term (λ (x)
                      (if (@ (fc/c X any CON_1 ρ ,l) (@ car x Λ) Λ)
                          (@ (fc/c X any CON_2 ρ ,r) (@ cdr x Λ) Λ)
                          #f))))))
   (where #t (proves AV cons?))]
  [(fc/c X any (cons/c CON_1 CON_2) ρ AV)
   (λ (X)
     (amb/e *black-hole*
            #f
            (if (@ EXP_1 *black-hole* Λ)
                (@ EXP_2 *black-hole* Λ)
                #f)))
   (where EXP_1 (fc/c X any CON_1 ρ (join-contracts)))
   (where EXP_2 (fc/c X any CON_2 ρ (join-contracts)))
                  
   ;; using *black-hole* instead of (car X) and (cdr X) avoids spurious blame of the language
   ;; (proj-{left,right} AV) can't produce anything interesting here, 
   ;; b/c then either AV is an or/c (impossible), or AV is a cons/c (also impossible)
   (where #f (proves AV cons?))
   (where #f (refutes AV cons?))])


(test 
 (test-equal 
  (term (flat-check ((pred exact-nonnegative-integer? f) (env)) (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) #t) (env (*black-hole* (-- ((∧) (env)))))))))
 (test-equal
  (term (flat-check ((pred exact-nonnegative-integer? f) (env)) (-- (clos "x" (env)))))
  (term (-- (clos (λ (x) #f) (env (*black-hole* (-- ((∧) (env)))))))))
 (test-equal
  (term (flat-check ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) (@ (prime? ^ f g) x f)) (env (*black-hole* (-- ((∧) (env)))))))))
 (test-equal
  (term (flat-check ((not/c (pred (prime? ^ f g) f)) (env)) (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) (if (@ (fc/e ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env)))) x Λ) #f #t))
                  (env (*black-hole* (-- ((∧) (env)))))))))
 (test-equal
  (term (flat-check ((and/c (pred (prime? ^ f g) f)
                            (pred (composite? ^ f g) f)) 
                     (env)) 
                    (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) (if (@ (fc/e ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env)))) x Λ)
                             (@ (fc/e ((pred (composite? ^ f g) f) (env)) (-- (clos 0 (env)))) x Λ) #f))
                  (env (*black-hole* (-- ((∧) (env)))))))))
 (test-equal 
  (term (flat-check ((or/c (pred (prime? ^ f g) f)
                           (pred (composite? ^ f g) f)) 
                     (env)) 
                    (-- (clos 0 (env)))))
  (term (-- (clos (λ (x) (if (@ (fc/e ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env)))) x Λ)
                             #t 
                             (@ (fc/e ((pred (composite? ^ f g) f) (env)) (-- (clos 0 (env)))) x Λ)))
                  (env (*black-hole* (-- ((∧) (env)))))))))
                  
 (test-equal 
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- (cons (-- (clos 0 (env))) (-- (clos 1 (env)))))))
  (term 
   (-- (clos (λ (x) (if (@ (fc/e ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env))))
                           (@ car x Λ) Λ)
                        (@ (fc/e ((pred (composite? ^ f g) f) (env)) (-- (clos 1 (env))))
                           (@ cdr x Λ) Λ) #f))
                  (env (*black-hole* (-- ((∧) (env)))))))))
 (test-equal
  (term (flat-check ((rec/c z (pred (prime? ^ f g) f)) (env)) (-- (clos 0 (env)))))
  (term (flat-check ((pred (prime? ^ f g) f) (env)) (-- (clos 0 (env))))))
 
 (test-equal
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- ((pred cons? f) (env)))))
  (term (-- (clos (λ (x) (@ (λ (x) (if (@ (λ (x) (@ (prime? ^ f g) x f))
                                          (@ car x Λ) Λ)
                                       (@ (λ (x) (@ (composite? ^ f g) x f))
                                          (@ cdr x Λ) Λ) #f)) x Λ))
                  (env (*black-hole* (join-contracts)))))))
 
 (test-equal 
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- ((∧) (env)))))
  (term (-- (clos (λ (x1)
                    (amb/e *black-hole* 
                           #f
                           (if (@ (fc/e ((pred (prime? ^ f g) f) (env)) (join-contracts)) *black-hole* Λ)
                               (@ (fc/e ((pred (composite? ^ f g) f) (env)) (join-contracts)) *black-hole* Λ)
                               #f)))
                  (env (*black-hole* (join-contracts)))))))
 (test-equal
  (term (flat-check ((rec/c x (or/c (pred empty? †)
                                    (cons/c (pred zero? †) x)))
                     (env))
                    (-- ((∧) (env)))))
  (term (-- (clos (λ (x1)
                    (if (@ (fc/e ((pred empty? †) (env)) (join-contracts)) x1 Λ)
                        #t
                        (@ (λ (x1) (amb/e *black-hole*
                                                    #f 
                                                    (if (@ (fc/e ((pred zero? †) (env)) (join-contracts)) *black-hole* Λ)
                                                        (@ (λ (x1) #t) *black-hole* Λ)
                                                        #f)))
                           x1 Λ)))
                  (env (*black-hole* (join-contracts))))))))