#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide subst/α subst/β subst/C subst/μ replace)
(test-suite test subst)

;; There are 4 kinds of substitutions
;; * β (and let) : ((x V) ...) E -> E
;; * α renaming : ((x x) ...) E -> E
;; * dependent contract β : ((x V) ...) C -> C
;; * μ : x C C -> C
;; All substituted values are closed

;; There is also a raw replacement, used only for define-contract:
;; * replace : any any any -> any

(define-metafunction λc~
  subst/β : ((x V) ...) E -> E
  [(subst/β ((x V) ...) E)
   (subst/αβ ((x V) ...) E)])

(define-metafunction λc~
  subst/α : ((x x) ...) E -> E
  [(subst/α ((x x_*) ...) E)
   (subst/αβ ((x x_*) ...) E)])

(define-metafunction λc~
  subst/αβ : SUBST E -> E
  ;; V
  [(subst/αβ SUBST (-- C*-top_0 C*-top ...))
   (-- C*-top_0 C*-top ...)]
  [(subst/αβ SUBST (any <= ℓ_1 ℓ_2 V_1 ℓ_3 V_2))
   (any <= ℓ_1 ℓ_2 
        (subst/αβ SUBST V_1) ℓ_3 
        (subst/αβ SUBST V_2))]
  ; only for CESK*, so do nothing
  [(subst/αβ SUBST blessed-A) blessed-A] 
  [(subst/αβ SUBST (-- PV C* ...))
   (-- (subst/αβ SUBST PV) C* ...)]
  
  [(subst/αβ SUBST V_0) V_0]  
  ;; PV
  [(subst/αβ SUBST (cons V_1 V_2))
   (cons (subst/αβ SUBST V_1)
         (subst/αβ SUBST V_2))]
  [(subst/αβ SUBST (λ (x_1 ...) E))
   (λ (x_1 ...) (subst/αβ (subst-minus SUBST (x_1 ...)) E))]
  [(subst/αβ SUBST (λ x_f (x_1 ...) E))
   (λ (x_1 ...) (subst/αβ (subst-minus SUBST (x_f x_1 ...)) E))]
  [(subst/αβ SUBST PV) PV]
  ;; --
  [(subst/αβ ((x_0 V_0) ... (x V) (x_1 V_1) ...) x) V]
  [(subst/αβ ((x_0 x_0*) ... (x x_*) (x_1 x_1*) ...) x) x_*]  
  [(subst/αβ SUBST x) x]  
  
  [(subst/αβ SUBST MODREF) MODREF]
  [(subst/αβ SUBST (@ E ... ℓ))
   (@ (subst/αβ SUBST E) ... ℓ)]
  [(subst/αβ SUBST (if E ...))
   (if (subst/αβ SUBST E) ...)]
  [(subst/αβ SUBST (@ o E ... ℓ))
   (@ o (subst/αβ SUBST E) ... ℓ)]  
  [(subst/αβ SUBST (let x_1 E_1 E_2))
   (let x_1 (subst/αβ SUBST E_1)
     (subst/αβ (subst-minus SUBST (x_1)) E_2))]
  [(subst/αβ SUBST (begin E ...))
   (begin (subst/αβ SUBST E) ...)]  
  [(subst/αβ SUBST AE) AE] ; not sure  
  [(subst/αβ SUBST (C <= ℓ_1 ℓ_2 V-or-AE ℓ_3 E))
   (C <= ℓ_1 ℓ_2 
      (subst/αβ SUBST V-or-AE)
      ℓ_3 
      (subst/αβ SUBST E))] 
  [(subst/αβ SUBST (blame ℓ_1 ℓ_2 V-or-AE any V_1))
   (blame ℓ_1 ℓ_2 (subst/αβ SUBST V-or-AE) any 
          (subst/αβ SUBST V_1))])

(define-metafunction λc~
  subst-minus : SUBST (x ...) -> SUBST
  [(subst-minus SUBST ()) SUBST]
  ;; V subst
  [(subst-minus ((x_1 V_1) ... (x V) (x_2 V_2) ...) (x x_3 ...))
   (subst-minus ((x_1 V_1) ... (x_2 V_2) ...) (x_3 ...))]
  [(subst-minus ((x_1 V_1) ...) (x x_2 ...))
   (subst-minus ((x_1 V_1) ...) (x_2 ...))]
  ;; x subst
  [(subst-minus ((x_1 x_1*) ... (x x_*) (x_2 x_2*) ...) (x x_3 ...))
   (subst-minus ((x_1 x_1*) ... (x_2 x_2*) ...) (x_3 ...))]
  [(subst-minus ((x_1 x_1*) ...) (x x_2 ...))
   (subst-minus ((x_1 x_1*) ...) (x_2 ...))])
  
  

(test
 ;; totality test
 (redex-check λc~ (side-condition (E ((x V) ...))
                                  (equal? (length (term (x ...)))
                                          (length (remove-duplicates (term (x ...))))))
              (begin (term (subst/β ((x V) ...) E))
                     #t))
 
  (redex-check λc~ (side-condition (E ((x x_*) ...))
                                  (equal? (length (term (x ...)))
                                          (length (remove-duplicates (term (x ...))))))
              (begin (term (subst/α ((x x_*) ...) E))
                     #t))
  
  (test-equal (term (subst/β ((x (-- 4))) x)) (term (-- 4)))
  (test-equal (term (subst/β ((x (-- 4))) (λ (x) x)))
              (term (λ (x) x)))
  (test-equal (term (subst/β ((y (-- 4))) (λ (x) y)))
              (term (λ (x) (-- 4))))
  (test-equal (term (subst/β ((x (-- 3)) (y (-- 4))) (λ (x z) (@ z x y f))))
              (term (λ (x z) (@ z x (-- 4) f))))
  
  (test-equal (term (subst/α ((x q)) x)) (term q))
  (test-equal (term (subst/α ((x q)) (λ (x) x)))
              (term (λ (x) x)))
  (test-equal (term (subst/α ((y q)) (λ (x) y)))
              (term (λ (x) q)))
  (test-equal (term (subst/α ((x q) (y r)) (λ (x z) (@ z x y f))))
              (term (λ (x z) (@ z x r f)))))

 
(define-metafunction λc~
  subst/C : SUBST any -> any ; really : SUBST C -> C
  [(subst/C SUBST (pred L ℓ))
   (pred (subst/αβ SUBST L) ℓ)]
  [(subst/C SUBST (any ...))
   ((subst/C SUBST any) ...)]
  [(subst/C ((x_1 x_2) ... (x x_*) (x_3 x_4) ...) x) x_*]   
  [(subst/C SUBST any) any])

(test
 (test-equal (term (subst/C ((X Z)) (or/c int? (cons/c X X))))
             (term (or/c int? (cons/c Z Z)))))

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

