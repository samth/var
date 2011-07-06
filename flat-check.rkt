#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "name.rkt" "meta.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test fc)

(define-metafunction λc~
  flat-check : (FLAT <= ℓ ℓ V-or-AE ℓ V) -> E
  [(flat-check (FLAT <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V))  
   (flat-check/defun FLAT V
                     (remember-contract V FLAT)
                     (blame ℓ_1 ℓ_3 V-or-AE FLAT V))])

(test 
 (test-equal
  (term (flat-check ((cons/c (pred (λ (x) (@ 1 0 blame-me)) p) (pred (λ (x) (@ 2 3 blame-me2)) p))
                     <= f g (-- 0) h
                     (-- (pred cons? f)))))
  (term (if (@ (λ (x) (@ 1 0 blame-me)) (-- (pred (λ (x) #t) Λ)) p)
            (if (@ (λ (x) (@ 2 3 blame-me2)) (-- (pred (λ (x) #t) Λ)) p)
                (-- (pred cons? f) (cons/c (pred (λ (x) (@ 1 0 blame-me)) p) (pred (λ (x) (@ 2 3 blame-me2)) p)))
                (blame f h (-- 0) (pred (λ (x) (@ 2 3 blame-me2)) p) (-- (pred (λ (x) #t) Λ))))
            (blame f h (-- 0) (pred (λ (x) (@ 1 0 blame-me)) p) (-- (pred (λ (x) #t) Λ)))))))


;; the continuation ranges over: B | E.
(define-metafunction λc~
  meta-defun-apply : E C V -> E
  [(meta-defun-apply (blame ℓ_1 ℓ_2 V-or-AE C_0 V_0) C V)
   (blame ℓ_1 ℓ_2 V-or-AE C V)]
  [(meta-defun-apply E C V)
   E])

(define-metafunction λc~
  flat-check/defun : FLAT V E E_k -> E
  [(flat-check/defun FLAT V E E_k)
   (fc/c () FLAT V E E_k)])


(define-metafunction λc~
  fc/c : ((C V) ...) FLAT V E E_k -> E
  [(fc/c (any_1 ... (C V) any_2 ...) C V E E_k) E]  
  [(fc/c any anyc V E E_k) E]
  [(fc/c any C V E E_k)
   E 
   (where #t (contract-in C V))]
  [(fc/c any (and/c FLAT_0 FLAT_1) V E E_k)
   (fc/c any FLAT_0 V (fc/c any FLAT_1 V E E_k) E_k)]
  [(fc/c any (cons/c FLAT_0 FLAT_1)
         (-- (cons V_0 V_1) C ...)
         E E_k)
   (fc/c any FLAT_0 V_0 (fc/c any FLAT_1 V_1 E E_k) E_k)]
  [(fc/c any C V E E_k)
   (meta-defun-apply E_k C V)
   (where #t (contract-not-in C V))]
  [(fc/c any (pred SV ℓ) V E E_k)
   (if (@ SV V ℓ) 
       E 
       (meta-defun-apply E_k (pred SV ℓ) V))]  
  [(fc/c any (or/c FLAT_0 FLAT_1) V E E_k)
   (fc/c any FLAT_0 V
         E
         (fc/c any FLAT_1 V E 
               (meta-defun-apply E_k (or/c FLAT_0 FLAT_1) V)))]  
  [(fc/c any (rec/c x C) V E E_k)
   (fc/c (((rec/c x C) V) . any) (unroll (rec/c x C)) V E E_k)]
  
  [(fc/c any (cons/c C_1 C_2) AV E E_k)
   (amb E_r ...)      
   (where (E_r ...)
          ,(for*/list ([l (term (proj-left AV))]
                       [r (term (proj-right AV))])
             (term (fc/c any C_1 ,l (fc/c any C_2 ,r E (meta-defun-apply E_k C_2 ,r)) (meta-defun-apply E_k C_1 ,l)))))   
   (where #t (proves AV cons?))]  
  [(fc/c any (cons/c C_1 C_2) AV E E_k) 
   (amb E_r (meta-defun-apply E_k (cons/c C_1 C_2) AV))
   (where E_r
          (fc/c any C_1 (-- (any/c)) (fc/c any C_2 (-- (any/c)) E (meta-defun-apply E_k C_2 (-- (any/c)))) 
                (meta-defun-apply E_k C_1 (-- (any/c)))))
   
   (where #f (proves AV cons?))
   (where #f (refutes AV cons?))]  
  )


(test
 
 (redex-check λc~ ((side-condition FLAT_1 (term (valid? FLAT_1))) V E E_k) (redex-match λc~ E (term (flat-check/defun FLAT_1 V E E_k))))
 
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
             (term (blame f1 f1 (-- 0) (nat/c) (-- "s"))))
 
 )