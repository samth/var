#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide subst/μ #;replace)
(test-suite test subst)

(define-metafunction λcρ
  subst/μ : X CON CON -> CON
  [(subst/μ X CON X) CON]
  [(subst/μ X CON X_0) X_0]
  [(subst/μ X CON (and/c CON_0 CON_1))
   (and/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]
  [(subst/μ X CON (or/c CON_0 CON_1))
   (or/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]
  [(subst/μ X CON (cons/c CON_0 CON_1))
   (cons/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]  
  [(subst/μ X CON (rec/c X CON_1))
   (rec/c X CON_1)]
  [(subst/μ X CON (rec/c X_1 CON_1))
   (rec/c X_1 (subst/μ X CON CON_1))]  
  [(subst/μ X CON (CON_1 ... -> CON_2))
   ((subst/μ X CON CON_1) ... -> (subst/μ X CON CON_2))]  
  [(subst/μ X CON (CON_1 ... -> (λ (X_1 ...) CON_2))) ; distinct class of variables
   ((subst/μ X CON CON_1) ... -> (λ (X_1 ...) (subst/μ X CON CON_2)))]   
  [(subst/μ X CON (pred any LAB))
   (pred any LAB)])


(test
 ;; totality test
 (redex-check λcρ (X CON_1 CON_2) (term (subst/μ X CON_1 CON_2))))