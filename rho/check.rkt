#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt" "demonic.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test check)

(define-metafunction λcρ
  flat-check : (FLAT ρ) V -> EXP
  [(flat-check (FLAT ρ) V)
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
  [(fc/c X any (atom/c ATOMLIT LAB) ρ V)
   (λ (X) (@ eqv? X ATOMLIT Λ))]
  [(fc/c X any (and/c FLAT_1 FLAT_2) ρ V)
   (λ (X) (IFF (@@ EXP_1 X Λ) (@@ EXP_2 X Λ) #f))
   (where EXP_1 (fc/c X any FLAT_1 ρ V))
   (where EXP_2 (fc/c X any FLAT_2 ρ V))]
  [(fc/c X any (not/c FLAT_1) ρ V)
   (λ (X) (IFF (@@ EXP X Λ) #f #t))
   (where EXP (fc/c X any FLAT_1 ρ V))]
  [(fc/c X any (cons/c FLAT_1 FLAT_2) ρ (-- (cons V_1 V_2) C ...))
   (λ (X) (IFF (@@ EXP_1 (@ car X Λ) Λ) (@@ EXP_2 (@ cdr X Λ) Λ) #f))
   (where EXP_1 (fc/c X any FLAT_1 ρ V_1))
   (where EXP_2 (fc/c X any FLAT_2 ρ V_2))]
  [(fc/c X any (pred PREDV LAB) ρ V)
   ;; η-expansion for right blame label in case PREDV is not a predicate.
   (λ (X) (@ PREDV X LAB))]
  [(fc/c X any (or/c FLAT_1 FLAT_2) ρ V)
   (λ (X) (IFF (@@ EXP_1 X Λ) #t (@@ EXP_2 X Λ)))
   (where EXP_1 (fc/c X any FLAT_1 ρ V))
   (where EXP_2 (fc/c X any FLAT_2 ρ V))]
  [(fc/c X_1 any (rec/c X CON) ρ V)   
   (fc/c X_1 ((((rec/c X CON) ρ) V) . any) (unroll (rec/c X CON)) ρ V)]
  [(fc/c X any (cons/c CON_1 CON_2) ρ AV)
   (λ (X) (amb/e (@@ EXP_n X Λ) ...))
   (where (EXP_n ...)
          ,(remove-duplicates
            (for*/list ([l (term (proj-left AV))]
                        [r (term (proj-right AV))])
              (term (λ (x)
                      ;; this is neccessary because you might have gotten here through a proj-left/right
                      ;; and therefore in the reduction semantics you don't know that this is actually a cons
                      (IFF (@@ cons? x Λ) 
                           (IFF (@@ (fc/c X any CON_1 ρ ,l) (@ car x Λ) Λ)
                                (@@ (fc/c X any CON_2 ρ ,r) (@ cdr x Λ) Λ)
                                #f)
                           ;; final result is #t b/c this is a spurious result if we get here
                           #t)))))) 
   (where #t (proves AV cons?))]
  [(fc/c X any (cons/c CON_1 CON_2) ρ AV)
   (λ (x)
     (IFF (@@ cons? x Λ)
          (IFF (@@ EXP_1 • Λ)
               (@@ EXP_2 • Λ)
              #f)
          #F))
   (where EXP_1 (fc/c X any CON_1 ρ (join-contracts)))
   (where EXP_2 (fc/c X any CON_2 ρ (join-contracts)))
                  
   ;; using • instead of (car X) and (cdr X) avoids spurious blame of the language
   ;; (proj-{left,right} AV) can't produce anything interesting here, 
   ;; b/c then either AV is an or/c (impossible), or AV is a cons/c (also impossible)
   (where #f (proves AV cons?))
   (where #f (refutes AV cons?))]
  
  ;; struct/c
  [(fc/c X any (struct/c X_m X_tag FLAT ...) ρ (-- (struct X_m X_tag V ...) C ...))
   (λ (X) (AND (@@ EXP EXP_1 Λ) ...))
   (where (EXP ...) ((fc/c X any FLAT ρ V) ...))
   (where (EXP_1 ...) ,(for/list ([i (length (term (V ...)))])
                         (term (@@ (s-ref X_m X_tag ,i) X Λ))))]
  
  [(fc/c X any (struct/c X_m X_tag CON ...) ρ AV)
   (λ (X) (amb/e (@@ EXP_n X Λ) ...))
   (where (EXP_n ...)
          ,(remove-duplicates
            (let ()
              (define all-combos
                (apply xprod (for/list ([i (length (term (CON ...)))])
                               (term (proj-struct AV X_m X_tag ,i)))))
              (for/list ([c (in-list all-combos)])
                (redex-let λcρ
                           ([(AV ...) c]
                            [(EXP_acc ...) (for/list ([i (length (term (CON ...)))])
                                             (term (s-ref X_m X_tag ,i)))])
                           (term (λ (x)
                                   ;; this is neccessary because you might have gotten here through a proj-left/right
                                   ;; and therefore in the reduction semantics you don't know that this is actually a cons
                                   (IFF (@@ ((tag->pred X_tag) ^ Λ X_m) x Λ)
                                        (AND (@@ (fc/c X any CON ρ AV) (@ EXP_acc x Λ) Λ) ...)
                                        ;; final result is #t b/c this is a spurious result if we get here
                                        #t))))))))
   (where #t (proves AV (s-pred X_m X_tag)))]
  [(fc/c X any (struct/c X_m X_tag FLAT ...) ρ AV)
   (λ (x) (AND (@@ (s-pred X_m X_tag) x Λ)
               (@@ EXP • Λ) ...))
   (where (EXP ...) ((fc/c X any FLAT ρ (join-contracts)) ...))
                  
   ;; using • instead of the results of the accessors avoids spurious blame of the language
   ;; (proj-struct n AV) can't produce anything interesting here, 
   ;; b/c then either AV is an or/c (impossible), or AV is a struct/c (also impossible)   
   (where #f (proves AV (s-pred X_m X_tag)))
   (where #f (refutes AV (s-pred X_m X_tag)))])


(test 
 (test-equal 
  (term (flat-check ((pred exact-nonnegative-integer? f) (env)) (-- (↓ 0 (env)))))
  (term (λ (x) #t)))
 (test-equal
  (term (flat-check ((pred exact-nonnegative-integer? f) (env)) (-- (↓ "x" (env)))))
  (term (λ (x) #f)))
 (test-equal
  (term (flat-check ((pred (prime? ^ f g) f) (env)) (-- (↓ 0 (env)))))
  (term (λ (x) (@ (prime? ^ f g) x f))))
 (test-equal
  (term (flat-check ((not/c (pred (prime? ^ f g) f)) (env)) (-- (↓ 0 (env)))))
  (term (λ (x) (if (@@ (flat-check ((pred (prime? ^ f g) f) (env)) (-- (↓ 0 (env)))) x Λ) #f #t))))        
 (test-equal
  (term (flat-check ((and/c (pred (prime? ^ f g) f)
                            (pred (composite? ^ f g) f)) 
                     (env)) 
                    (-- (↓ 0 (env)))))
  (term (λ (x) (if (@@ (flat-check ((pred (prime? ^ f g) f) (env)) (-- (↓ 0 (env)))) x Λ)
                   (@@ (flat-check ((pred (composite? ^ f g) f) (env)) (-- (↓ 0 (env)))) x Λ) #f))))        
 (test-equal 
  (term (flat-check ((or/c (pred (prime? ^ f g) f)
                           (pred (composite? ^ f g) f)) 
                     (env)) 
                    (-- (↓ 0 (env)))))
  (term (λ (x) (if (@@ (flat-check ((pred (prime? ^ f g) f) (env)) 
                                  (-- (↓ 0 (env)))) x Λ)
                   #t 
                   (@@ (flat-check ((pred (composite? ^ f g) f) (env)) 
                                  (-- (↓ 0 (env)))) x Λ)))))
 (test-equal 
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- (cons (-- (↓ 0 (env))) (-- (↓ 1 (env)))))))
  (term 
   (λ (x) (if (@@ (flat-check ((pred (prime? ^ f g) f) (env)) (-- (↓ 0 (env))))
                 (@ car x Λ) Λ)
              (@@ (flat-check ((pred (composite? ^ f g) f) (env)) (-- (↓ 1 (env))))
                 (@ cdr x Λ) Λ) #f))))
 (test-equal
  (term (flat-check ((rec/c z (pred (prime? ^ f g) f)) (env)) (-- (↓ 0 (env)))))
  (term (flat-check ((pred (prime? ^ f g) f) (env)) (-- (↓ 0 (env))))))
 
 (test-equal
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- ((pred cons? f) (env)))))
  (term (λ (x) (@ (λ (x) (if (@ (λ (x) (@ (prime? ^ f g) x f))
                                          (@ car x Λ) Λ)
                                       (@ (λ (x) (@ (composite? ^ f g) x f))
                                          (@ cdr x Λ) Λ) #f)) x Λ))))         
 (test-equal 
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     (env))
                    (-- ((∧) (env)))))
  (term (λ (x1)
          (amb/e #f
                 (if (@@ (flat-check ((pred (prime? ^ f g) f) (env)) (join-contracts)) • Λ)
                     (@@ (flat-check ((pred (composite? ^ f g) f) (env)) (join-contracts)) • Λ)
                     #f)))))        
 (test-equal
  (term (flat-check ((rec/c x (or/c (pred empty? †)
                                    (cons/c (pred zero? †) x)))
                     (env))
                    (-- ((∧) (env)))))
  (term (λ (x1)
          (if (@@ (flat-check ((pred empty? †) (env)) (join-contracts)) x1 Λ)
              #t
              (@@ (λ (x1) (amb/e #f 
                                (if (@ (flat-check ((pred zero? †) (env)) (join-contracts)) • Λ)
                                    (@ (λ (x1) #t) • Λ)
                                    #f)))
                 x1 Λ))))))
 