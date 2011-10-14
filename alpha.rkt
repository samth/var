#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "subst.rkt" "util.rkt")
(provide ≡α)
(test-suite test alpha)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ≡α
         
;; Is E_0 ≡α E_1 by systematic renaming.
(define-metafunction λc~
  ≡α : E E -> #t or #f
  [(≡α E E) #t]
  [(≡α (-- (cons V_1 V_2) C*_1 ...)
       (-- (cons V_3 V_4) C*_2 ...))
   (≡α V_2 V_4)
   (where #t (≡α V_3 V_4))
   (where (#t ...) ((≡α/C C*_1 C*_2) ...))]
  [(≡α (-- L_1 C*_1 ...)       
       (-- L_2 C*_2 ...))
   (≡α L_1 L_2)
   (where (#t ...) ((≡α/C C*_1 C*_2) ...))]
  ; all other Vs must be syntactically identical.    
  [(≡α (cons V_1 V_2)
       (cons V_3 V_4))
   (≡α V_2 V_4)
   (where #t (≡α V_1 V_3))]
  [(≡α (λ (x_1 ..._1) E_1)
       (λ (x_2 ..._1) E_2))
   (≡α (subst/α ((x_1 x_1*) ...) E_1)
       (subst/α ((x_2 x_1*) ...) E_2))
   (where (x_1* ...) 
          ,(variables-not-in (term (E_1 E_2)) (term (x_1 ...))))]
  [(≡α (λ x_f1 (x_1 ..._1) E_1)
       (λ x_f2 (x_2 ..._1) E_2))
   (≡α (subst/α ((x_f1 x_f*) (x_1 x_1*) ...) E_1)
       (subst/α ((x_f1 x_f*) (x_2 x_1*) ...) E_2))
   (where (x_f* x_1* ...) 
          ,(variables-not-in (term (E_1 E_2)) (term (x_f1 x_1 ...))))]
  ; all other PVs must be syntactically identical.  
  [(≡α (@ E_1 E_2 ... ℓ) 
       (@ E_3 E_4 ... ℓ))
   (≡α E_1 E_3)
   (where (#t ...) ((≡α E_2 E_4) ...))]
  [(≡α (if E_1 E_2 E_3)
       (if E_4 E_5 E_6))
   (≡α E_3 E_6)
   (where (#t ...) 
          ((≡α E_1 E_4)
           (≡α E_2 E_5)))]
  [(≡α (@ o E_1 ... ℓ)
       (@ o E_2 ... ℓ))
   #t
   (where (#t ...) ((≡α E_1 E_2) ...))]  
  [(≡α (let x_1 E_1 E_2)
       (let x_2 E_3 E_4))
   (≡α (subst/α ((x_1 x_fresh)) E_2)
       (subst/α ((x_2 x_fresh)) E_4))
   (where #t (≡α E_1 E_3))
   (where x_fresh ,(variable-not-in (term (E_2 E_4)) (term x_1)))]
  [(≡α (begin E_1 E_2)
       (begin E_3 E_4))
   (≡α E_2 E_4)
   (where #t (≡α E_1 E_3))]
  [(≡α E_1 E_2) #f])
  
;; doesn't do α for μ-bound or dependent λ-bound vars.
(define-metafunction λc~
  ≡α/C : C C -> #t or #f
  [(≡α/C C C) #t]
  [(≡α/C (pred L_1 ℓ)
         (pred L_2 ℓ))
   (≡α L_1 L_2)]
  [(≡α/C C C) #f])

(test
 (test-equal (term (≡α (λ (x) x) (λ (y) y))) #t)
 (test-equal (term (≡α (λ (x) x) (λ (y) z))) #f)
 (test-equal (term (≡α 3 3)) #t)
 (test-equal (term (≡α 3 4)) #f)
 (test-equal (term (≡α (@ (λ (x) x) 3 f) (@ (λ (y) y) 3 f))) #t)
 (test-equal (term (≡α (@ (λ (x) x) (λ (y) y) f) (@ (λ (y) y) (λ (x) x) f))) #t)
 
 ;; Syntactic identity implies ≡α.
 (redex-check λc~ E (term (≡α E E)))
 
 ;; All fresh substitions preserve ≡α.
 (redex-check λc~ (E (x ...))
              (redex-let λc~ ([(x_* ...) (variables-not-in (term E) (term (x ...)))])
                         (term (≡α E (subst/α ((x x_*) ...) E))))))
              
 
 
 