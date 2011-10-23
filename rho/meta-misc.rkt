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
  [(arity (-- ((CON_0 ... -> CON_1) ρ) C ...))
   ,(length (term (CON_0 ...)))]
  [(arity (-- ((CON_0 ... -> (λ (X ...) CON_1)) ρ) C ...))
   ,(length (term (CON_0 ...)))]
  [(arity (-- C)) #f]
  [(arity (-- C_0 C ...))
   (arity (-- C ...))]
  [(arity ((CON ... --> any) ρ <= LAB_0 LAB_1 V_b LAB_2 any_0))
   ,(length (term (CON ...)))])

(test
 (test-equal (term (arity (-- (clos (λ () x) ())))) 0)
 (test-equal (term (arity (-- (clos (λ (x y z) x) ())))) 3)
 (test-equal (term (arity (-- (clos (λ f (x y z) x) ())))) 3)
 (test-equal (term (arity (-- (((pred string? f) (pred string? g) -> (pred string? h)) ())))) 2)
 (test-equal (term (arity (-- (((pred string? f) (pred string? g) -> (λ (x y) (pred string? h))) ())))) 2)
 (test-equal (term (arity (-- ((pred string? h) ()) (((pred string? f) (pred string? g) -> (pred string? h)) ())))) 2)
 (test-equal (term (arity (-- ((pred procedure? f) ())))) #f)
 (test-equal (term (arity ((--> (pred string? †)) () <= f g (-- (clos 0 ())) f (-- (clos (λ () 1) ()))))) 0)
 )

;; Is C_1 /\ C_2 inhabited
(define-metafunction λcρ
  feasible : C C -> #t or #f
  [(feasible ATOMC CONSC) #f]
  [(feasible CONSC ATOMC) #f]
  [(feasible NOTPROCC ARROWC) #f]
  [(feasible ARROWC NOTPROCC) #f]  
  [(feasible ATOMC_1 ATOMC_2) 
   ,(or (term (implies ATOM?_1 ATOM?_2))
        (term (implies ATOM?_2 ATOM?_1)))
   (where ((pred ATOM?_1 LAB_1) ρ_1) ATOMC_1)
   (where ((pred ATOM?_2 LAB_2) ρ_2) ATOMC_2)]
  [(feasible C_1 C_2) #t])

(define-metafunction λcρ
  implies : ATOM? ATOM? -> #t or #f
  [(implies ATOM? ATOM?) #t]
  [(implies zero? exact-nonnegative-integer?) #t]  
  [(implies false? boolean?) #t]
  [(implies ATOM?_1 ATOM?_2) #f])

(define-metafunction λcρ
  join-contracts : C ... -> AV
  [(join-contracts C ...)
   (remember-contract (-- (pred (λ (x) #t) Λ)) C ...)])

;; FIXME: this should rely on a ≡C metafunction that, eg.
;; compares modrefs without regard to use sites.
;; FIXME: don't need to remember arity-like contracts on arity-known procedures.
(define-metafunction λcρ
  remember-contract : V C ... -> V ; or AE
  ;; Expand away and/c
  [(remember-contract V ((and/c CON_1 CON_2) ρ) C ...)
   (remember-contract V (CON_1 ρ) (CON_2 ρ) C ...)] 
  ;; drop boring contracts on concrete flat values
  #;
  [(remember-contract (-- FV C_1 ...) FC C ...)
   (remember-contract (-- FV C_1 ...) C ...)]
  [(remember-contract (-- PREVAL C_0 ...) ((pred OP LAB) ρ) C ...)
   (remember-contract (-- PREVAL C_0 ...) C ...)] 
  ;; drop any/c on the floor when possible
  [(remember-contract (-- C C_1 ... ((pred (λ (X) #t) LAB) ρ)) C_2 ...)
   (remember-contract (-- C C_1 ...) C_2 ...)] 
  [(remember-contract (-- ((pred (λ (X) #t) LAB) ρ) C C_1 ...) C_2 ...)
   (remember-contract (-- C C_1 ...) C_2 ...)]
  [(remember-contract (-- ((pred (λ (X) #t) LAB) ρ)) C C_2 ...)
   (remember-contract (-- C) C_2 ...)]
  [(remember-contract V ((pred (λ (X) #t) LAB) ρ) C_2 ...)
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
  [(remember-contract (-- PREVAL C_1 ...) C_2 C ...)
   (remember-contract (-- PREVAL C_1 ... C_2) C ...)
   (where (#t ...) ((feasible C_2 C_1) ...))]  
  ;; drop infeasible contracts
  [(remember-contract (-- any_0 C_1 ...) C_2 C ...)
   (remember-contract (-- any_0 C_1 ...) C ...)]   
  ;; push remembered contracts past blessed arrows
  [(remember-contract (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) C_0 ...)
   (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2
           (remember-contract V C_0 ...))]
  ;; FIXME pretty sure this case is dead or just for addresses.
  #;
  [(remember-contract ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 any_1) C_0 ...)
   ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 any_1)]  
  ;; we're done
  [(remember-contract V) V])

(test
 ;; flatten and/c
 (test-equal (term (remember-contract (-- ((pred string? f) ()))
                                      ((and/c (pred (f? ^ f g) m)
                                              (pred (h? ^ h j) n))
                                       ())))
             (term (-- ((pred string? f) ())
                       ((pred (f? ^ f g) m) ())
                       ((pred (h? ^ h j) n) ()))))
 ;; infeasible
 (test-equal (term (remember-contract (-- ((pred string? f) ())) ((pred zero? g) ())))
             (term (-- ((pred string? f) ()))))
 ;; feasible
 (test-equal (term (remember-contract (-- ((pred exact-nonnegative-integer? f) ())) ((pred zero? g) ())))
             (term (-- ((pred exact-nonnegative-integer? f) ())
                       ((pred zero? g) ()))))
 ;; drop any
 (test-equal (term (remember-contract (-- ((pred string? f) ())) ((pred (λ (x) #t) g) ())))
             (term (-- ((pred string? f) ()))))
 (test-equal (term (remember-contract (-- ((pred string? f) ())
                                          ((pred (λ (x) #t) g) ()))))
             (term (-- ((pred string? f) ()))))
 (test-equal (term (remember-contract (-- ((pred (λ (x) #t) g) ())
                                          ((pred string? f) ()))))
             (term (-- ((pred string? f) ()))))
 (test-equal (term (remember-contract (-- ((pred (λ (x) #t) g) ()))
                                      ((pred string? f) ())))
             (term (-- ((pred string? f) ()))))
 
 ;; drop duplicates
 (test-equal (term (remember-contract (-- ((pred (p? ^ f g) f) ())) ((pred (p? ^ f g) f) ())))
             (term (-- ((pred (p? ^ f g) f) ()))))
 (test-equal (term (remember-contract (-- (clos 0 ()) 
                                          ((pred (p? ^ f g) f) ()))
                                      ((pred (p? ^ f g) f) ())))
             (term (-- (clos 0 ()) 
                       ((pred (p? ^ f g) f) ()))))
 
 ;; push past blessed arrow
 (test-equal (term (remember-contract ((--> (pred (p? ^ f g) f))
                                       () <= f g (-- (clos 0 ())) f 
                                       (-- (clos (λ () "x") ())))
                                      ((pred (q? ^ h j) f) ())))
             (term ((--> (pred (p? ^ f g) f))
                    () <= f g (-- (clos 0 ())) f 
                    (-- (clos (λ () "x") ())
                        ((pred (q? ^ h j) f) ()))))))

;; FIXME
#|
 ;; check that remember-contract is total and produces the right type
 (redex-check λc~ (V C ...)              
              (or (not (term (valid-value? V)))
                  (ormap not (term ((valid? C) ...)))
                  (redex-match λc~ V-or-AE (term (remember-contract V C ...)))))
|#

;; All domain contracts of all function contracts in given contracts.
;; produces a list of the list of contracts for each argument of a function.

;; In case of arity mismatch, we take the first function contract as canonical
;; just like `arity'.
(define-metafunction λcρ
  domain-contracts : (C ...) -> ((C ...) ...)
  [(domain-contracts (C ...))
   (domain-contracts* (C ...) ())])

(define-metafunction λcρ
  domain-contracts* : (C ...) ((C ...) ...) -> ((C ...) ...)
  [(domain-contracts* () any) any]
  [(domain-contracts* (((CON_1 ... -> any) ρ) C ...) ())
   (domain-contracts* (C ...) (((CON_1 ρ)) ...))]
  [(domain-contracts* (((CON_1 ..._1 -> any) ρ) C ...) ((C_3 ...) ..._1))
   (domain-contracts* (C ...) ((C_3 ... (CON_1 ρ)) ...))]
  [(domain-contracts* (C_0 C ...) any)
   (domain-contracts* (C ...) any)])

(test
  (test-equal (term (domain-contracts (((pred string? f) ()))))
             (term ()))
  (test-equal (term (domain-contracts ((((pred exact-nonnegative-integer? f) 
                                         (pred string? f) -> 
                                         (pred exact-nonnegative-integer? f)) 
                                        ())
                                       (((pred boolean? f) 
                                         (pred empty? f) -> 
                                         (pred exact-nonnegative-integer? f)) 
                                        ()))))
              (term ((((pred exact-nonnegative-integer? f) ()) ((pred boolean? f) ()))
                     (((pred string? f) ()) ((pred empty? f) ()))))))

;; All range contracts of all function contracts in given contracts.
;; given the specified arguments for dependent contracts
;; throw out all ranges when the arity doesn't match the supplied number of values
(define-metafunction λcρ
  range-contracts : (C ...) (V ...) -> (C ...)
  [(range-contracts () any) ()]
  [(range-contracts (((CON_1 ..._1 -> CON_2) ρ) C ...) (V ..._1))
   ((CON_2 ρ) C_0 ...)
   (where (C_0 ...) (range-contracts (C ...) (V ...)))]
  [(range-contracts (((CON_1 ..._1 -> (λ (X ..._1) CON_2)) ρ) C ...) (V ..._1))
   ((CON_2 (env-extend ρ (X V) ...)) C_0 ...)
   (where (C_0 ...) (range-contracts (C ...) (V ...)))]
  [(range-contracts (C_0 C ...) any) 
   (range-contracts (C ...) any)])

(test
 (test-equal (term (range-contracts (((pred string? f) ())) ()))
             (term ()))
 (test-equal (term (range-contracts ((((pred exact-nonnegative-integer? f) 
                                       (pred string? f) -> 
                                       (pred exact-nonnegative-integer? f)) 
                                      ())
                                     (((pred boolean? f) 
                                       (pred empty? f) -> 
                                       (pred exact-nonnegative-integer? f)) 
                                      ()))
                                    ((-- (clos 0 ())) (-- (clos 9 ())))))
             (term (((pred exact-nonnegative-integer? f) ())
                    ((pred exact-nonnegative-integer? f) ()))))
 (test-equal (term (range-contracts ((((pred exact-nonnegative-integer? f) 
                                       -> (λ (x) (pred (λ (y) (@ = x y f)) f))) ()))
                                    ((-- (clos 0 ())))))
             (term (((pred (λ (y) (@ = x y f)) f) ((x (-- (clos 0 ())))))))))


(define-metafunction λcρ
  env-extend : ρ (X V) ... -> ρ
  [(env-extend ((X_1 V_1) ...) (X_2 V_2) ...)
   ((X_2 V_2) ... (X_1 V_1) ...)])