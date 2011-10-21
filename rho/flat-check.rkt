#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "meta.rkt" #;"alpha.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test fc)

(define-metafunction λcρ
  flat-check : (FLAT ρ) V -> D
  [(flat-check (FLAT ρ) V) 
   (-- (clos (fc/c X () FLAT ρ V) ρ))
   (where X ,(variable-not-in (term (FLAT V)) 'x))])

(define-metafunction λcρ
  fc/c : X ((CON V) ...) FLAT ρ V -> EXP
  [(fc/c X (any_1 ... (CON V) any_2 ...) CON ρ V) (λ (x) #t)]
  ;; Why did we bother with something like this?
  ;;[(fc/c X any anyc V) (λ (x) #t)]  
  [(fc/c X any CON ρ V)
   (λ (X) #t)
   (where #t (contract-in (CON ρ) V))]
  [(fc/c X any CON ρ V)
   (λ (X) #f)
   (where #t (contract-not-in (CON ρ) V))] 
  [(fc/c X any (and/c FLAT_0 FLAT_1) ρ V)
   (λ (X)
     (if (@ (fc/c X any FLAT_0 ρ V) X Λ)
         (@ (fc/c X any FLAT_1 ρ V) X Λ)
         #f))]
  [(fc/c X any (cons/c FLAT_0 FLAT_1) ρ
         (-- (cons V_0 V_1) C ...))
   (λ (X)
     (if (@ (fc/c X any FLAT_0 ρ V_0) (@ car X Λ) Λ)
         (@ (fc/c X any FLAT_1 ρ V_1) (@ cdr X Λ) Λ)
         #f))] 
  [(fc/c X any (pred PREDV LAB) ρ V)
   (λ (X) (@ PREDV X LAB))]  
  [(fc/c X any (or/c FLAT_0 FLAT_1) ρ V)
   (λ (X)
     (if (@ (fc/c X any FLAT_0 ρ V) X Λ) 
         #t
         (@ (fc/c X any FLAT_1 ρ V) X Λ)))]  
  [(fc/c X_1 any (rec/c X C) ρ V)   
   (fc/c X_1 (((rec/c X C) V) . any) (unroll (rec/c X C)) ρ V)]
  )
  #|
  [(fc/c x any (cons/c C_1 C_2) AV)
   (amb E_r ...)
   (where (E_r ...)
          ,(remove-duplicates
            (for*/list ([l (term (proj-left AV))]
                        [r (term (proj-right AV))])
              (term (λ (x) (if (@ cons? x Λ)
                               (if (@ (fc/c x any C_1 ,l) (@ first x Λ) Λ)
                                   (@ (fc/c x any C_2 ,r) (@ rest x Λ) Λ)
                                   #f)
                               #t))))))
   (where #t (proves AV cons?))]  
  [(fc/c x any (cons/c C_1 C_2) AV)
   (λ (x) (amb (if (@ (fc/c x any C_1 (-- (any/c))) (-- (any/c)) Λ)
                   (@ (fc/c x any C_2 (-- (any/c))) (-- (any/c)) Λ)
                   #f)
               #f))
   (where #f (proves AV cons?))
   (where #f (refutes AV cons?))]
  )
|#


(test
 ;; FIXME uncomment
 #;
 (redex-check λcρ ((side-condition FLAT_1 (term (valid? FLAT_1))) V)
              (redex-match λcρ E (term (flat-check FLAT_1 V))))
 

 (test-equal (term (flat-check ((and/c (pred exact-nonnegative-integer? f) (pred empty? f)) ())
                               (-- (clos #t ()))))
             '(λ (x) #f))
 )
#|
 (test-equal (term (flat-check (string/c) (-- "Plain"))) '(λ (x) #t))
 (test-equal (term (flat-check (bool/c) (-- #t))) '(λ (x) #t))
 (test-equal (term (≡α (flat-check (any/c) (-- 0)) (λ (x) #t)))
             #t)
 (test-equal (term (flat-check (cons/c (nat/c) (nat/c))
                               (-- (cons (-- 0) (-- 1)))))
             '(λ (x) #t))
 (test-equal (term (flat-check (pred (λ (z) z) ℓ) (-- 0)))
             (term (λ (x) (@ (λ (z) z) x ℓ))))
 ;; recursive contracts
 (test-equal (term (flat-check (rec/c R (or/c (empty/c) (cons/c (nat/c) R)))
                               (-- 0)))
             '(λ (x) #f))
 (test-equal (term (flat-check (rec/c R (or/c (empty/c) (cons/c (nat/c) R)))
                               (-- empty)))
             '(λ (x) #t))
 
 (test-equal (term (flat-check (rec/c R (or/c (empty/c) (cons/c (nat/c) R)))
                               (-- (cons (-- 0) (-- empty)))))
             '(λ (x) (if (@ (λ (x) #f) x Λ) #t (@ (λ (x) (if (@ (λ (x) #t) (@ first x Λ) Λ) (@ (λ (x) #t) (@ rest x Λ) Λ) #f)) x Λ))))
 ;; Commented out for enormousness
 #;
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- (cons (-- 0) (-- (cons (-- 0) (-- empty))))) #t #f))
             #t)
 #;
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- (cons (-- "0") (-- empty))) #t #f))
             #f)
 
 (test-equal (term (flat-check (cons/c (cons/c (nat/c) (nat/c)) (nat/c)) (-- (cons (-- (cons (-- "s") (-- "t"))) (-- "u")))))
             (term (λ (x) #f)))

 )
 |#