#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide subst/β subst/C subst/μ)
(test-suite test subst)

;; There are 3 kinds of substitutions
;; * β (and let) : ((x V) ...) E -> E
;; * dependent contract β : ((x V) ...) C -> C
;; * μ : x C C -> C
;; All substituted values are closed

;; There is also a raw replacement, used only for define-contract:
;; * replace : any any any -> any

;; {x/V,...}E
;; Never substitutes inside contracts
(define-metafunction λc~ 
  subst/β : ((x V) ...) E -> E
  ;; V
  [(subst/β ((x V) ...) (-- C*-top_0 C*-top ...))
   (-- C*-top_0 C*-top ...)]
  [(subst/β ((x V) ...) (any <= ℓ_1 ℓ_2 V_1 ℓ_3 V_2))
   (any <= ℓ_1 ℓ_2 
        (subst/β ((x V) ...) V_1) ℓ_3 
        (subst/β ((x V) ...) V_2))]
  ; only for CESK*, so do nothing
  [(subst/β ((x V) ...) blessed-A) blessed-A] 
  [(subst/β ((x V) ...) (-- PV C* ...))
   (-- (subst/β ((x V) ...) PV) C* ...)]
  
  [(subst/β ((x V) ...) V_0) V_0]  
  ;; PV
  [(subst/β ((x V) ...) (cons V_1 V_2))
   (cons (subst/β ((x V) ...) V_1)
         (subst/β ((x V) ...) V_2))]
  [(subst/β ((x V) ...) (λ (x_1 ...) E))
   (λ (x_1 ...) (subst/β (subst-minus ((x V) ...) (x_1 ...)) E))]
  [(subst/β ((x V) ...) (λ x_f (x_1 ...) E))
   (λ (x_1 ...) (subst/β (subst-minus ((x V) ...) (x_f x_1 ...)) E))]
  [(subst/β ((x V) ...) PV) PV]
  ;; --
  [(subst/β ((x_0 V_0) ... (x V) (x_1 V_1) ...) x) V]
  [(subst/β ((x_0 V_0) ...) x) x]  
  [(subst/β ((x V) ...) MODREF) MODREF]
  [(subst/β ((x V) ...) (@ E ... ℓ))
   (@ (subst/β ((x V) ...) E) ... ℓ)]
  [(subst/β ((x V) ...) (if E ...))
   (if (subst/β ((x V) ...) E) ...)]
  [(subst/β ((x V) ...) (@ o E ... ℓ))
   (@ o (subst/β ((x V) ...) E) ... ℓ)]  
  [(subst/β ((x V) ...) (let x_1 E_1 E_2))
   (let x_1 (subst/β ((x V) ...) E_1)
     (subst/β (subst-minus ((x V) ...) (x_1)) E_2))]
  [(subst/β ((x V) ...) (begin E ...))
   (begin (subst/β ((x V) ...) E) ...)]  
  [(subst/β ((x V) ...) AE) AE] ; not sure  
  [(subst/β ((x V) ...) (C <= ℓ_1 ℓ_2 V-or-AE ℓ_3 E))
   (C <= ℓ_1 ℓ_2 
      (subst/β ((x V) ...) V-or-AE)
      ℓ_3 
      (subst/β ((x V) ...) E))] 
  [(subst/β ((x V) ...) (blame ℓ_1 ℓ_2 V-or-AE any V_1))
   (blame ℓ_1 ℓ_2 (subst/β ((x V) ...) V-or-AE) any 
          (subst/β ((x V) ...) V_1))])

(define-metafunction λc~
  subst-minus : ((x V) ...) (x ...) -> ((x V) ...)
  [(subst-minus ((x V) ...) ()) ((x V) ...)]
  [(subst-minus ((x_1 V_1) ... (x V) (x_2 V_2) ...) (x x_3 ...))
   (subst-minus ((x_1 V_1) ... (x_2 V_2) ...) (x_3 ...))]
  [(subst-minus ((x_1 V_1) ...) (x x_2 ...))
   (subst-minus ((x_1 V_1) ...) (x_2 ...))])

(test
 ;; totality test
 (redex-check λc~ (side-condition (E ((x V) ...))
                                  (equal? (length (term (x ...)))
                                          (length (remove-duplicates (term (x ...))))))
              (begin (term (subst/β ((x V) ...) E))
                     #t))
 
 (test-equal (term (subst/β ((x (-- 4))) x)) (term (-- 4)))
 (test-equal (term (subst/β ((x (-- 4))) (λ (x) x)))
             (term (λ (x) x)))
 (test-equal (term (subst/β ((y (-- 4))) (λ (x) y)))
             (term (λ (x) (-- 4))))
 (test-equal (term (subst/β ((x (-- 3)) (y (-- 4))) (λ (x z) (@ z x y f))))
             (term (λ (x z) (@ z x (-- 4) f))))) 
 
(define-metafunction λc~
  subst/C : ((x V) ...) any -> any ; really : ((x V) ...) C -> C
  [(subst/C ((x V) ...) (pred L ℓ))
   (pred (subst/β ((x V) ...) L) ℓ)]
  [(subst/C ((x V) ...) (any ...))
   ((subst/C ((x V) ...) any) ...)]
  [(subst/C ((x V) ...) any) any])

(define-metafunction λc~
  subst/μ : x C C -> C
  [(subst/μ x C x) C]
  [(subst/μ x C x_0) x_0]
  [(subst/μ x C (and/c C_0 C_1))
   (and/c (subst/μ x C C_0) (subst/μ x C C_1))]
  [(subst/μ x C (or/c C_0 C_1))
   (or/c (subst/μ x C C_0) (subst/μ x C C_1))]
  [(subst/μ x C (cons/c C_0 C_1))
   (cons/c (subst/μ x C C_0) (subst/μ x C C_1))]  
  [(subst/μ x C (rec/c x C_1))
   (rec/c x C_1)]
  [(subst/μ x C (rec/c x_1 C_1))
   (rec/c x_1 (subst/μ x C C_1))]  
  [(subst/μ x C (C_1 ... -> C_2))
   ((subst/μ x C C_1) ... -> (subst/μ x C C_2))]  
  [(subst/μ x C (C_1 ... -> (λ (x_1 ...) C_2))) ; distinct class of variables
   ((subst/μ x C C_1) ... -> (λ (x_1 ...) (subst/μ x C C_2)))]   
  [(subst/μ x C (pred any ℓ))
   (pred any ℓ)])

(test
 ;; totality test
 (redex-check λc~ (x C_1 C_2) (term (subst/μ x C_1 C_2))))


(define-metafunction λc~
  replace : any any any -> any
  [(replace any any_1 any) any_1]
  [(replace any_1 any_2 (any_3 ...))
   ((replace any_1 any_2 any_3) ...)]
  [(replace any any_1 any_2) any_2])

(test
 (test-equal (term (replace x 3 x)) (term 3))
 (test-equal (term (replace (y) 3 ((y) (y) (y)))) (term (3 3 3)))
 (test-equal (term (replace x 3 (q r s))) (term (q r s))))

