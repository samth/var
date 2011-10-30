#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "meta.rkt" #;"alpha.rkt")
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
   (-- (clos (λ (X) #t) ()))
   (where #t (≡C C (FLAT ρ)))]                                          
  ;; Why did we bother with something like this?
  ;;[(fc/c X any anyc V) (λ (x) #t)]  
  [(fc/c X any FLAT ρ V)
   (-- (clos (λ (X) #t) ()))
   (where #t (contract-in (FLAT ρ) V))]
  [(fc/c X any FLAT ρ V)
   (-- (clos (λ (X) #f) ()))
   (where #t (contract-not-in (FLAT ρ) V))]  
  [(fc/c X any (and/c FLAT_1 FLAT_2) ρ V)
   (-- (clos (λ (X) (if (@ f1 X Λ) (@ f2 X Λ) #f))
             ((f1 (fc/c X any FLAT_1 ρ V))
              (f2 (fc/c X any FLAT_2 ρ V)))))]
  [(fc/c X any (cons/c FLAT_1 FLAT_2) ρ
         (-- (cons V_1 V_2) C ...))
   (-- (clos (λ (X) (if (@ f1 (@ car X Λ) Λ) (@ f2 (@ cdr X Λ) Λ) #f))
             ((f1 (fc/c X any FLAT_1 ρ V_1))
              (f2 (fc/c X any FLAT_2 ρ V_2)))))]
  [(fc/c X any (pred PREDV LAB) ρ V)
   ;; η-expansion for right blame label in case PREDV is not a predicate.
   (-- (clos (λ (X) (@ PREDV X LAB)) ρ))]
  [(fc/c X any (or/c FLAT_1 FLAT_2) ρ V)
   (-- (clos (λ (X) (if (@ f1 X Λ) #t (@ f2 X Λ)))
             ((f1 (fc/c X any FLAT_1 ρ V))
              (f2 (fc/c X any FLAT_2 ρ V)))))]
  [(fc/c X_1 any (rec/c X CON) ρ V)   
   (fc/c X_1 ((((rec/c X CON) ρ) V) . any) (unroll (rec/c X CON)) ρ V)]    
  [(fc/c X any (cons/c CON_1 CON_2) ρ AV)
   (amb D_r ...)
   (where (D_r ...)
          ,(remove-duplicates
            (for*/list ([l (term (proj-left AV))]
                        [r (term (proj-right AV))])
              (term (-- (clos (λ (x) (if (@ cons? X Λ)
                                         (if (@ f1 (@ car X Λ) Λ)
                                             (@ f2 (@ cdr X Λ) Λ)
                                             #f)
                                         #t)))
                        ((f1 (fc/c X any CON_1 ρ ,l))
                         (f2 (fc/c X any CON_2 ρ ,r))))))))  
   (where #t (proves AV cons?))]  
  [(fc/c X any (cons/c CON_1 CON_2) AV)
   (amb (-- (clos (λ (X) #f) ()))        
        (-- (clos (λ (X)
                    (if (@ f1 *black-hole* Λ)
                        (@ f2 *black-hole* Λ)
                        #f))
                  ((f1 (fc/c X any CON_1 (join-contracts)))
                   (f2 (fc/c X any CON_2 (join-contracts)))
                   (*black-hole* (join-contracts))))))
   (where #f (proves AV cons?))
   (where #f (refutes AV cons?))])


(test 
 (test-equal 
  (term (flat-check ((pred exact-nonnegative-integer? f) ()) (-- (clos 0 ()))))
  (term (-- (clos (λ (x) #t) ()))))
 (test-equal
  (term (flat-check ((pred exact-nonnegative-integer? f) ()) (-- (clos "x" ()))))
  (term (-- (clos (λ (x) #f) ()))))
 (test-equal
  (term (flat-check ((pred (prime? ^ f g) f) ()) (-- (clos 0 ()))))
  (term (-- (clos (λ (x) (@ (prime? ^ f g) x f)) ()))))
 (test-equal
  (term (flat-check ((and/c (pred (prime? ^ f g) f)
                            (pred (composite? ^ f g) f)) 
                     ()) 
                    (-- (clos 0 ()))))
  (term (-- (clos (λ (x) (if (@ f1 x Λ) (@ f2 x Λ) #f))
                  ((f1 (flat-check ((pred (prime? ^ f g) f) ()) (-- (clos 0 ()))))
                   (f2 (flat-check ((pred (composite? ^ f g) f) ()) (-- (clos 0 ())))))))))
 (test-equal 
  (term (flat-check ((or/c (pred (prime? ^ f g) f)
                           (pred (composite? ^ f g) f)) 
                     ()) 
                    (-- (clos 0 ()))))
  (term (-- (clos (λ (x) (if (@ f1 x Λ) #t (@ f2 x Λ)))
                  ((f1 (flat-check ((pred (prime? ^ f g) f) ()) (-- (clos 0 ()))))
                   (f2 (flat-check ((pred (composite? ^ f g) f) ()) (-- (clos 0 ())))))))))
 (test-equal 
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     ())
                    (-- (cons (-- (clos 0 ())) (-- (clos 1 ()))))))
  (term (-- (clos (λ (x) (if (@ f1 (@ car x Λ) Λ) (@ f2 (@ cdr x Λ) Λ) #f))
                  ((f1 (flat-check ((pred (prime? ^ f g) f) ()) (-- (clos 0 ()))))
                   (f2 (flat-check ((pred (composite? ^ f g) f) ()) (-- (clos 1 ())))))))))
 (test-equal
  (term (flat-check ((rec/c z (pred (prime? ^ f g) f)) ()) (-- (clos 0 ()))))
  (term (flat-check ((pred (prime? ^ f g) f) ()) (-- (clos 0 ())))))
 
 ;; FIXME : needs work on abs-δ before this can work.
 (test-equal
  (term (flat-check ((cons/c (pred (prime? ^ f g) f)
                             (pred (composite? ^ f g) f)) 
                     ())
                    (-- ((pred cons? f) ()))))
  #f)
 
 ;; FIXME need case for cons/c vs. (-- any/c).
 ;; FIXME need case for recursive loop that hits co-inductive base case.
 )

