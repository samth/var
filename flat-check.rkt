#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "meta.rkt" "alpha.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test fc)

(define-metafunction λc~
  flat-check : FLAT V -> E
  [(flat-check FLAT V) 
   (fc/c x () FLAT V)
   (where x ,(variable-not-in (term (FLAT V)) 'x))])


(define-metafunction λc~
  fc/c : x ((C V) ...) FLAT V -> E
  [(fc/c x (any_1 ... (C V) any_2 ...) C V) (λ (x) #t)]
  [(fc/c x any anyc V) (λ (x) #t)]
  [(fc/c x any C V)
   (λ (x) #t)
   (where #t (contract-in C V))]
  [(fc/c x any C V)
   (λ (x) #f)
   (where #t (contract-not-in C V))]
  [(fc/c x any (and/c FLAT_0 FLAT_1) V)
   (λ (x)
     (if (@ (fc/c x any FLAT_0 V) x Λ)
         (@ (fc/c x any FLAT_1 V) x Λ)
         #f))]
  [(fc/c x any (cons/c FLAT_0 FLAT_1)
         (-- (cons V_0 V_1) C ...))
   (λ (x)
     (if (@ (fc/c x any FLAT_0 V_0) (@ first x Λ) Λ)
         (@ (fc/c x any FLAT_1 V_1) (@ rest x Λ) Λ)
         #f))]  
  [(fc/c x any (pred SV ℓ) V)
   (λ (x) (@ SV x ℓ))]  
  [(fc/c x any (or/c FLAT_0 FLAT_1) V)
   (λ (x)
     (if (@ (fc/c x any FLAT_0 V) x Λ) 
         #t
         (@ (fc/c x any FLAT_1 V) x Λ)))]  
  [(fc/c x_1 any (rec/c x C) V)   
   (fc/c x_1 (((rec/c x C) V) . any) (unroll (rec/c x C)) V)]
  
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

(test
 
 (redex-check λc~ ((side-condition FLAT_1 (term (valid? FLAT_1))) V)
              (redex-match λc~ E (term (flat-check FLAT_1 V))))
  
 (test-equal (term (flat-check (and/c (pred exact-nonnegative-integer? f) (pred empty? f)) (-- #t)))
             '(λ (x) #f))
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
 