#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
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


(define-metafunction λcρ
  remember-contract : V C ... -> V
  [(remember-contract V C ...) V])  ;; FIXME placeholder
#|
(define-metafunction λc~
  remember-contract : V-or-AE C ... -> V or AE
  ;; Expand away and/c
  [(remember-contract V-or-AE (and/c C_1 C_2) C ...)
   (remember-contract V-or-AE C_1 C_2 C ...)]
  ;; drop boring contracts on concrete flat values
  [(remember-contract (-- FV C_1 ...) FC C ...)
   (remember-contract (-- FV C_1 ...) C ...)]
  [(remember-contract (-- PV C_0 ...) (pred o? ℓ) C ...)
   (remember-contract (-- PV C_0 ...) C ...)]
  ;; drop any/c on the floor when possible
  [(remember-contract (-- anyc C C_1 ...) C_2 ...)
   (remember-contract (-- C C_1 ...) C_2 ...)]
  [(remember-contract (-- anyc) C C_2 ...)
   (remember-contract (-- C) C_2 ...)]
  [(remember-contract V anyc C_2 ...)
   (remember-contract V C_2 ...)]
  ;; do the real work
  ;; forget duplicates
  [(remember-contract (-- any_0 C_0 ... C C_1 ...) C C_2 ...)
   (remember-contract (-- any_0 C_0 ... C C_1 ...) C_2 ...)]
  [(remember-contract (-- C_0 ... C C_1 ...) C C_2 ...)
   (remember-contract (-- C_0 ... C C_1 ...) C_2 ...)]
  ;; add feasible non-duplicates
  [(remember-contract (-- C_1 ...) C_2 C ...)
   (remember-contract (-- C_1 ... C_2) C ...)
   (where (#t ...) ((feasible C_2 C_1) ...))] 
  [(remember-contract (-- PV C_1 ...) C_2 C ...)
   (remember-contract (-- PV C_1 ... C_2) C ...)
   (where (#t ...) ((feasible C_2 C_1) ...))]
  ;; drop infeasible contracts
  [(remember-contract (-- any_0 C_1 ...) C_2 C ...)
   (remember-contract (-- any_0 C_1 ...) C ...)]  
  ;; push remembered contracts past blessed arrows
  [(remember-contract ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 V) C_0 ...)
   ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2
                     (remember-contract V C_0 ...))]
  [(remember-contract ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 any_1) C_0 ...)
   ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 any_1)]
  ;; we're done
  [(remember-contract V-or-AE) V-or-AE])

(test 
 (test-equal (term (remember-contract ((--> (any/c)) <= f g (-- 0) h (-- (any/c))) (nat/c)))
             (term ((--> (any/c)) <= f g (-- 0) h (-- (nat/c)))))
 
 (test-equal (term (remember-contract (-- (λ (x) x)) (pred procedure? Λ)))
             (term (-- (λ (x) x))))
 (test-equal (term (remember-contract (-- 1) (nat/c)))
             (term (-- 1)))
 (test-equal (term (remember-contract (-- (any/c) (nat/c))))
             (term (-- (nat/c))))
 
 ;; check that remember-contract is total and produces the right type
 (redex-check λc~ (V C ...)              
              (or (not (term (valid-value? V)))
                  (ormap not (term ((valid? C) ...)))
                  (redex-match λc~ V-or-AE (term (remember-contract V C ...))))))
|#