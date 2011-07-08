#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "meta.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test fc)

(define-metafunction λc~
  flat-check : FLAT V -> E
  [(flat-check FLAT V) 
   (fc/c x () FLAT V)
   (where x ,(variable-not-in (term (FLAT V)) 'x))])


(define-metafunction λc~
  fc/c : x ((C V) ...) FLAT V -> E ;; FIXME add x
  [(fc/c x (any_1 ... (C V) any_2 ...) C V) (λ (x) #t)]
  [(fc/c x any anyc V) (λ (x) #t)]
  [(fc/c x any C V)
   (λ (x) #t)
   (where #t (contract-in C V))]
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
  [(fc/c x any C V)
   (λ (x) #f)
   (where #t (contract-not-in C V))]
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
              (term (λ (x) (if (@ (fc/c x any C_1 ,l) (@ first x Λ) Λ)
                               (@ (fc/c x any C_2 ,r) (@ rest x Λ) Λ)
                               #f))))))   
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
 
 ;; FIXME: tests from flat-check/defun.  Fix up for flat-check.
 #|
 (test-equal (term (proves (-- #t) bool?)) #t)
 (test-equal (term (flat-check ((and/c (pred nat? f) (pred empty? f)) <= f1 f2 (-- "V") f1 (-- #t))))
             (term (blame f1 f1 (-- "V") (pred nat? f) (-- #t))))
 (test-equal (term (flat-check/defun (string/c) (-- "Plain") #t #f)) #t)
 (test-equal (term (flat-check/defun (bool/c) (-- #t) #t #f)) #t)
 (test-equal (term (flat-check/defun (any/c) (-- 0) #t #f)) #t)
 (test-equal (term (flat-check/defun (cons/c (nat/c) (nat/c))
                                     (-- (cons (-- 0) (-- 1)))
                                     #t
                                     #f))
             #t)
 (test-equal (term (flat-check/defun (pred (λ (x) x) ℓ) (-- 0) #t #f))
             (term (if (@ (λ (x) x) (-- 0) ℓ)
                       #t
                       #f)))
 ;; recursive contracts
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- 0) #t #f))
             #f)
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- empty) #t #f))
             #t)
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- (cons (-- 0) (-- empty))) #t #f))
             #t)
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- (cons (-- 0) (-- (cons (-- 0) (-- empty))))) #t #f))
             #t)
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- (cons (-- "0") (-- empty))) #t #f))
             #f)
 
 (test-equal (term (flat-check ((cons/c (cons/c (nat/c) (nat/c)) (nat/c)) <= f1 f2 (-- 0) f1
                                                                          (-- (cons (-- (cons (-- "s") (-- "t"))) (-- "u"))))))
             (term (blame f1 f1 (-- 0) (nat/c) (-- "s")))
|#
 )
 