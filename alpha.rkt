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
  [(≡α (-- PV_1 C_1 ...)
       (-- PV_2 C_2 ...))
   (≡α PV_1 PV_2)   
   (where (#t ...) ((≡α/C C_1 C_2) ...))]
  [(≡α ((C_1 ..._1 --> (λ (x_1 ..._1) C_2)) <= ℓ_1 ℓ_2 V_1 ℓ_3 V_2)
       ((C_3 ..._1 --> (λ (x_2 ..._1) C_4)) <= ℓ_1 ℓ_2 V_3 ℓ_3 V_4))
   (≡α/C (subst/C ((x_1 x_1*) ...) C_2)
         (subst/C ((x_2 x_1*) ...) C_4))
   (where (#t ...) ((≡α/C C_1 C_3) ...))
   (where (#t ...) ((≡α V_1 V_3) (≡α V_2 V_4)))
   (where (x_1* ...) ,(variables-not-in (term (C_2 C_4))
                                        (term (x_1 ...))))]
  ; all other Vs must be syntactically identical.    
  [(≡α (cons V_1 V_2)
       (cons V_3 V_4))
   (≡α V_2 V_4)
   (where #t (≡α V_1 V_3))]
  [(≡α (struct x V_1 ...)
       (struct x V_2 ...))
   #t
   (where (#t ...) ((≡α V_1 V_2) ...))]
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
  [(≡α (let ((x_1 E_1) ..._1) E_2)
       (let ((x_2 E_3) ..._1) E_4))
   (≡α (subst/α ((x_1 x_fresh) ...) E_2)
       (subst/α ((x_2 x_fresh) ...) E_4))
   (where (#t ...) ((≡α E_1 E_3) ...))
   (where (x_fresh ...) ,(variables-not-in (term (E_2 E_4)) (term (x_1 ...))))]
  [(≡α (begin E_1 E_2)
       (begin E_3 E_4))
   (≡α E_2 E_4)
   (where #t (≡α E_1 E_3))]
  [(≡α E_1 E_2) #f])
  
(define-metafunction λc~
  ≡α/C : C C -> #t or #f
  [(≡α/C C C) #t]
  [(≡α/C (C_1 ..._1 -> (λ (x_1 ..._2) C_2))
         (C_3 ..._1 -> (λ (x_2 ..._2) C_4)))
   (≡α/C (subst/C ((x_1 x_1*) ...) C_2)
         (subst/C ((x_2 x_1*) ...) C_4))
   (where (#t ...) ((≡α/C C_1 C_3) ...))
   (where (x_1* ...) ,(variables-not-in (term (C_2 C_4))
                                        (term (x_1 ...))))]
  [(≡α/C (rec/c x_1 C_1) (rec/c x_2 C_2))
   (≡α/C (subst/C ((x_1 x_*)) C_1)
         (subst/C ((x_2 x_*)) C_2))
   (where x_* ,(variable-not-in (term (C_1 C_2)) (term x_1)))]                 
  [(≡α/C (pred L_1 ℓ)
         (pred L_2 ℓ))
   (≡α L_1 L_2)]
  [(≡α/C C_1 C_2) #f])

(test
 (test-equal (term (≡α (λ (x) x) (λ (y) y))) #t)
 (test-equal (term (≡α (λ (x) x) (λ (y) z))) #f)
 (test-equal (term (≡α 3 3)) #t)
 (test-equal (term (≡α 3 4)) #f)
 (test-equal (term (≡α (-- (λ (x) x)) (-- (λ (y) y)))) #t)
 (test-equal (term (≡α (-- (λ (x) x)) (-- (λ (y) z)))) #f)
 (test-equal (term (≡α (-- 3) (-- 3))) #t)
 (test-equal (term (≡α (-- 3) (-- 4))) #f) 
 (test-equal (term (≡α (@ (λ (x) x) 3 f) (@ (λ (y) y) 3 f))) #t)
 (test-equal (term (≡α (@ (λ (x) x) (λ (y) y) f) (@ (λ (y) y) (λ (x) x) f))) #t)
 (test-equal (term (≡α (let ((x 1) (y 2)) x)
                       (let ((y 1) (x 2)) y)))
             #t)
 (test-equal (term (≡α (cons (-- (λ (x) x)) (-- (λ (y) y)))
                       (cons (-- (λ (y) y)) (-- (λ (z) z)))))
             #t)
 (test-equal (term (≡α (struct s (-- (λ (x) x)) (-- (λ (y) y)))
                       (struct s (-- (λ (y) y)) (-- (λ (z) z)))))
             #t) 
 (test-equal (term (≡α (((pred bool? f) --> (λ (x) (pred (λ (y) x) f))) <= f f (-- 0) f (-- (λ (z) z)))
                       (((pred bool? f) --> (λ (q) (pred (λ (y) q) f))) <= f f (-- 0) f (-- (λ (z) z)))))
             #t)
 
 (test-equal (term (≡α/C ((pred bool? f) -> (λ (x) (pred (λ (y) x) f)))
                         ((pred bool? f) -> (λ (q) (pred (λ (y) q) f)))))
             #t)
 
 (test-equal (term (≡α (-- 0 (rec/c X (or/c int? (cons/c X X))))
                       (-- 0 (rec/c Y (or/c int? (cons/c Y Y))))))
             #t)
 
 (test-equal (term (≡α/C (rec/c X (or/c int? (cons/c X X)))
                         (rec/c Y (or/c int? (cons/c Y Y)))))
             #t) 
                   
 ;; Syntactic identity implies ≡α.
 (redex-check λc~ E (term (≡α E E)))
 
 ;; All fresh substitions preserve ≡α.
 ;; COUNTEREXAMPLE: (q (q)) -- the statement is clearly false
 ;; I don't see how to clean it up
 #;
 (redex-check λc~ (E (x ...))
              (redex-let λc~ ([(x_* ...) (variables-not-in (term E) (term (x ...)))])
                         (term (≡α E (subst/α ((x x_*) ...) E))))))
              
 
 
 
