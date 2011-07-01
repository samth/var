#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "name.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test meta-misc)

;; If there are multiple arrows, we (arbitrarily) take the first arity.
(define-metafunction λc~
  arity : V -> number or #f
  [(arity (-- (λ x (x_0 ...) E) C ...))
   ,(length (term (x_0 ...)))]
  [(arity (-- (λ (x_0 ...) E) C ...))
   ,(length (term (x_0 ...)))]
  [(arity (-- (C_0 ... -> C_1) C ...))
   ,(length (term (C_0 ...)))]
  [(arity (-- (C_0 ... -> (λ (x ...) C_1)) C ...))
   ,(length (term (C_0 ...)))]
  [(arity (-- C)) #f]
  [(arity (-- C_0 C ...))
   (arity (-- C ...))])
  
(test
 (test-equal (term (arity (-- (λ () x)))) 0)
 (test-equal (term (arity (-- (λ (x y z) x)))) 3)
 (test-equal (term (arity (-- ((nat/c) (nat/c) -> (nat/c))))) 2)
 (test-equal (term (arity (-- ((nat/c) (nat/c) -> (λ (x y) (nat/c)))))) 2)
 (test-equal (term (arity (-- (string/c) ((nat/c) (nat/c) -> (nat/c))))) 2)
 (test-equal (term (arity (-- (pred proc? f)))) #f))


(define-metafunction λc~ 
  ∈ : any (any ...) -> #t or #f
  [(∈ any (any_0 ... (-- any) any_1 ...)) #t]
  [(∈ any_0 any_1) #f])


;; Is C_1 /\ C_2 inhabited
(define-metafunction λc~
  feasible : C C -> #t or #f
  [(feasible FC (cons/c C_1 C_2)) #f]
  [(feasible (cons/c C_1 C_2) FC) #f]
  [(feasible FC (C_1 ... -> any)) #f]
  [(feasible (C_1 ... -> any) FC) #f]
  [(feasible (cons/c C_a C_b) (C_1 ... -> any)) #f]
  [(feasible (C_1 ... -> any) (cons/c C_a C_b)) #f]
  [(feasible FC_1 FC_2) ,(equal? (term FC_1) (term FC_2))]
  [(feasible C_1 C_2) #t])
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remember-contract

(define-metafunction λc~
  remember-contract : V-or-AE C ... -> V or AE
  [(remember-contract V-or-AE) V-or-AE]
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
   (remember-contract (-- any_0 C_1 ...) C ...)])

(test
 (test-equal (term (remember-contract (-- (λ (x) x)) (pred proc? Λ)))
             (term (-- (λ (x) x))))
 (test-equal (term (remember-contract (-- 1) (nat/c)))
             (term (-- 1)))
 
 ;; check that remember-contract is total and produces the right type
 (redex-check λc~ (V C ...)              
              (or (not (term (valid-value? V)))
                  (ormap not (term ((valid? C) ...)))
                  (redex-match λc~ V-or-AE (term (remember-contract V C ...))))))


(define-metafunction λc~
  strip-concrete-contracts : V -> AV or PV
  [(strip-concrete-contracts (-- PV C ...)) PV]
  [(strip-concrete-contracts AV) AV])

;; All domain contracts of all function contracts in given contracts.
;; produces a list of the list of contracts for each argument of a function.

;; In case of arity mismatch, we take the first function contract as canonical
;; just like `arity'.
(define-metafunction λc~
  domain-contracts : (C ...) -> ((C ...) ...)
  [(domain-contracts (C ...))
   (domain-contracts* (C ...) ())])

(define-metafunction λc~
  domain-contracts* : (C ...) ((C ...) ...) -> ((C ...) ...)  
  [(domain-contracts* () any) any]
  [(domain-contracts* ((C_1 ... -> any) C ...) ())
   (domain-contracts* (C ...) ((C_1) ...))]
  [(domain-contracts* ((C_1 ..._1 -> any) C ...) ((C_3 ...) ..._1))
   (domain-contracts* (C ...) ((C_3 ... C_1) ...))]
  [(domain-contracts* (C_0 C ...) any)
   (domain-contracts* (C ...) any)])

(test
 (redex-check λc~ AV
              (if (term (∈ #t (δ (@ proc? AV ★))))
                  (= (term (arity AV))
                     (length (term (domain-contracts ,(cdr (term AV))))))
                  #t))
 
  (test-equal (term (domain-contracts (((nat/c) (string/c) -> (nat/c))
                                       ((bool/c) (empty/c) -> (nat/c)))))
              (term (((nat/c) (bool/c))
                     ((string/c) (empty/c)))))
  (test-equal (term (domain-contracts (((nat/c) (string/c) -> (nat/c))
                                       ((bool/c) -> (nat/c)))))
              (term (((nat/c)) ((string/c))))))

(define-metafunction λc~
  seq : E E ... -> E 
  [(seq E) E]
  [(seq E E_0 ...) (begin E (seq E_0 ...))])

;; All range contracts of all function contracts in given contracts.
;; given the specified arguments for dependent contracts
;; throw out all ranges when the arity doesn't match the supplied number of values
(define-metafunction λc~
  range-contracts : (C ...) (V ...) -> (C ...)
  [(range-contracts () any) ()]
  [(range-contracts ((C_1 ..._1 -> C_2) C ...) (V ..._1))
   (C_2 C_0 ...)
   (where (C_0 ...) (range-contracts (C ...) (V ...)))]
  [(range-contracts ((C_1 ..._1 -> (λ (x ..._1) C_2)) C ...) (V ..._1))
   ((subst* (x ...) (V ...) C_2) C_0 ...)
   (where (C_0 ...) (range-contracts (C ...) (V ...)))]
  [(range-contracts (C_0 C ...) any) 
   (range-contracts (C ...) any)])

(define-metafunction λc~
  ∧ : C ... -> C
  [(∧)  (any/c)]
  [(∧ C) C]
  [(∧ C_0 C_1  ...)
   (and/c C_0 (∧ C_1 ...))])

(test
 (test-equal (term (∧)) (term (any/c)))
 (test-equal (term (∧ (nat/c))) (term (nat/c)))
 (test-equal (term (∧ (nat/c) (string/c)))
             (term (and/c (nat/c) (string/c))))
 (test-equal (term (∧ (nat/c) (string/c) (empty/c)))
             (term (and/c (nat/c) (and/c (string/c) (empty/c))))))

;; Removes duplicate remembered contracts.
(define-metafunction λc~
  normalize : V -> V
  [(normalize (-- PV C ...)) (-- PV C_1 ...)
   (where (C_1 ...)
          ,(remove-duplicates (term (C ...))
                              (match-lambda**
                               [(`(,f ^ _) `(,f ^ _)) #t]
                               [(a b) (equal? a b)])))]
  [(normalize (-- C_0 C ...)) (-- C_0 C_1 ...)
   (where (C_1 ...)
          ,(remove-duplicates (term (C ...))
                              (match-lambda**
                               [(`(,f ^ _) `(,f ^ _)) #t]
                               [(a b) (equal? a b)])))])

(test
 (redex-check λc~ V  (redex-match λc~ V (term (normalize V)))))

(define-metafunction λc~
  explode : C -> (C ...)
  [(explode (or/c C_1 C_2))
   (C_1e ... C_2e ...)
   (where ((C_1e ...) (C_2e ...)) ((explode C_1) (explode C_2)))]  
  [(explode (rec/c x C))
   (explode (unroll (rec/c x C)))]  
  [(explode C) (C)])

(define-metafunction λc~
  unroll : (rec/c x C) -> C
  [(unroll (rec/c x C))
   (subst x (rec/c x C) C)])

(test
 (test-equal (term (explode (or/c (nat/c) (string/c))))
             (term ((nat/c) (string/c)))))
