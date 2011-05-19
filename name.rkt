#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide ≡α subst)
(test-suite test name)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; subst

(define-metafunction λc~ subst : x any any -> any 
  ;; 0. Don't substitue for module references.
  [(subst x any (f ^ ℓ)) (f ^ ℓ)]
  [(subst x any (@ any_1 ... ℓ))
   (@ (subst x any any_1) ... ℓ)]   
  ;; 1. x bound, so don't continue in λ body  
  [(subst x any_1 (λ x any_2)) 
   (λ x any_2)] 
  [(subst x any_1 (λ x_0 x any_2))
   (λ x_0 x any_2)]
  [(subst x any_1 (λ x x_0 any_2))
   (λ x_0 x any_2)]
  [(subst x any_1 (let x any_2 any_3))
   (let x (subst x any_1 any_2) any_3)]
  ;; 2. general purpose capture avoiding case  
  [(subst x_1 any_1 (λ x_2 any_2)) 
   (λ x_new
     (subst x_1 any_1 (subst-var x_2 x_new any_2))) 
   (where x_new 
          ,(variable-not-in (term (x_1 any_1 any_2)) 
                            (term x_2)))] 
  [(subst x_1 any_1 (λ x_2 x_3 any_2)) 
   (λ x_new1 x_new2
     (subst x_1 any_1 (subst-var x_2 x_new1 (subst-var x_3 x_new2 any_2))))
   (where (x_new1 x_new2)
          (,(variable-not-in (term (x_1 x_3 any_1 any_2)) 
                             (term x_2))
           ,(variable-not-in (term (x_1 x_2 any_1 any_2)) 
                             (term x_3))))]
  [(subst x_1 any_1 (let x_2 any_2 any_3))
   (let x_new
     (subst x_1 any_1 any_2)
     (subst x_1 any_1 (subst-var x_2 x_new any_2)))   
   (where x_new 
          ,(variable-not-in (term (x_1 any_1 any_2)) 
                            (term x_2)))]
  
  ;; 3. replace x_1 with e_1  
  [(subst x_1 any_1 x_1) any_1]  
  ;; 4. x_1 and x_2 are different, so don't replace  
  [(subst x_1 any_1 x_2) x_2]  
  ;; the last cases cover all other expressions  
  [(subst x_1 any_1 (any_2 ...)) 
   ((subst x_1 any_1 any_2) ...)] 
  [(subst x_1 any_1 any_2) 
   any_2])

(define-metafunction λc~ subst-var : x any any -> any 
  [(subst-var x_1 any_1 x_1) any_1] 
  [(subst-var x_1 any_1 (any_2 ...)) 
   ((subst-var x_1 any_1 any_2) ...)] 
  [(subst-var x_1 any_1 any_2) any_2])

(test
 (test-equal (term (subst x 0 x)) (term 0))
 (test-equal (term (subst x 0 y)) (term y))
 (test-equal (term (subst x 0 (λ x x))) (term (λ x x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ≡α

;; Is E_0 ≡α E_1 by systematic renaming.
(define-metafunction λc~
  ≡α : any any -> #t or #f
  [(≡α (λ x_0 any_0) (λ x_1 any_1))
   (≡α (subst x_0 x_fresh any_0)
       (subst x_1 x_fresh any_1))
   (where x_fresh ,(variable-not-in (term (any_0 any_1)) (term x_0)))]       
  [(≡α (λ x_f0 x_0 any_0) (λ x_f1 x_1 any_1))   
   (≡α (subst x_0 x_fresh (subst x_f0 x_ffresh any_0))
       (subst x_1 x_fresh (subst x_f1 x_ffresh any_1)))   
   (where x_ffresh ,(variable-not-in (term (any_0 any_1)) (term x_f0)))
   (where x_fresh  ,(variable-not-in (term (any_0 any_1 x_ffresh)) (term x_0)))]  
  [(≡α (let x_0 any_0 any_b0) (let x_1 any_1 any_b1))
   (≡α (subst x_0 x_fresh any_0)
       (subst x_1 x_fresh any_1))
   (where #t (≡α any_0 any_1))
   (where x_fresh ,(variable-not-in (term (any_0 any_1)) (term x_0)))]    
  [(≡α (any_0 ..._1) (any_1 ..._1))
   #t
   (where (#t ...) ((≡α any_0 any_1) ...))]
  [(≡α any any) #t]
  [(≡α any_0 any_1) #f])

(test
 (test-equal (term (≡α (λ x x) (λ y y))) #t)
 (test-equal (term (≡α (λ x x) (λ y z))) #f)
 (test-equal (term (≡α 3 3)) #t)
 (test-equal (term (≡α 3 4)) #f)
 (test-equal (term (≡α (@ (λ x x) 3 f) (@ (λ y y) 3 f))) #t)
 (test-equal (term (≡α (@ (λ x x) (λ y y) f) (@ (λ y y) (λ x x) f))) #t)
 
 (redex-check λc~ E (term (≡α E E))))