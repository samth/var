#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "subst.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test meta-misc)

(define-metafunction λcρ
  unroll : (rec/c X CON) -> CON
  [(unroll (rec/c X CON))
   (subst/μ X (rec/c X CON) CON)])

(test
 (redex-check λcρ (X CON) 
              (equal? (term (unroll (rec/c X CON)))
                      (term (subst/μ X (rec/c X CON) CON)))))

(define-metafunction λcρ 
  ∈ : any (any ...) -> #t or #f
  [(∈ any (any_0 ... (-- any) any_1 ...)) #t]
  [(∈ any (any_0 ... (-- (clos any ρ) C ...) any_1 ...)) #t]
  [(∈ any_0 any_1) #f])

;; If there are multiple arrows, we (arbitrarily) take the first arity.
(define-metafunction λcρ
  arity : PROC -> number or #f
  
  [(arity (-- (clos OP1 ρ) C ...)) 1]
  [(arity (-- (clos OP2 ρ) C ...)) 2]  
  
  [(arity (-- (clos (λ X (X_0 ...) EXP) ρ) C ...))
   ,(length (term (X_0 ...)))]
  [(arity (-- (clos (λ (X ...) EXP) ρ) C ...))
   ,(length (term (X ...)))]
  ;; ABSTRACT VALUES
  #|
  [(arity (-- (C_0 ... -> C_1) C ...))
   ,(length (term (C_0 ...)))]
  [(arity (-- (C_0 ... -> (λ (x ...) C_1)) C ...))
   ,(length (term (C_0 ...)))]
  [(arity (-- C)) #f]
  [(arity (-- C_0 C ...))
   (arity (-- C ...))]
  |#
  [(arity ((C ... --> any) <= LAB_0 LAB_1 V_b LAB_2 any_0))
   ,(length (term (C ...)))])
  
(test
 (test-equal (term (arity (-- (clos (λ () x) ())))) 0)
 (test-equal (term (arity (-- (clos (λ (x y z) x) ())))) 3)
 (test-equal (term (arity (-- (clos (λ f (x y z) x) ())))) 3)
 ;; FIXME: uncomment when doing ABSTRACT values
 #;(test-equal (term (arity (-- ((nat/c) (nat/c) -> (nat/c))))) 2)
 #;(test-equal (term (arity (-- ((nat/c) (nat/c) -> (λ (x y) (nat/c)))))) 2)
 #;(test-equal (term (arity (-- (string/c) ((nat/c) (nat/c) -> (nat/c))))) 2)
 #;(test-equal (term (arity (-- (pred procedure? f)))) #f)
 ;; FIXME: add blessed case
 )