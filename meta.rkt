#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "name.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test meta)

;; If there are multiple arrows, we (arbitrarily) take the first arity.
(define-metafunction λc~
  arity : V -> number or #f
  [(arity (-- (λ x (x_0 ...) E) C ...))
   ,(length (term (x_0 ...)))]
  [(arity (-- (λ (x_0 ...) E) C ...))
   ,(length (term (x_0 ...)))]
  [(arity (-- (C_0 ... -> C_1) C ...))
   ,(length (term (C_0 ...)))]
  [(arity (-- C)) #f]
  [(arity (-- C_0 C ...))
   (arity (-- C ...))])
  
(test
 (test-equal (term (arity (-- (λ () x)))) 0)
 (test-equal (term (arity (-- (λ (x y z) x)))) 3)
 (test-equal (term (arity (-- ((nat/c) (nat/c) -> (nat/c))))) 2)
 (test-equal (term (arity (-- (string/c) ((nat/c) (nat/c) -> (nat/c))))) 2)
 (test-equal (term (arity (-- (pred proc? f)))) #f))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metafunctions

(define-metafunction λc~ 
  ∈ : any (any ...) -> #t or #f
  [(∈ any (any_0 ... (-- any) any_1 ...)) #t]
  [(∈ any_0 any_1) #f])

(define-metafunction λc~
  demonic* : C V -> E
  [(demonic* C (-- PV C_0 ...))
   (@ (demonic C) (-- PV C_0 ...) ★)]
  [(demonic* C V) ;; produces trivial expression
   (-- 0)])

(define-metafunction λc~
  amb : E E ... -> E
  [(amb E) E]
  [(amb E_1 E_2 ...) (if (-- (any/c)) E_1 (amb E_2 ...))])

;; Produce a function that will do "everything" it can
;; to its argument while treating it as a C.
;; The only important part is that functions are applied
;; to all possible values.  Note that this requires traversing
;; pairs.
(define-metafunction λc~
  demonic : C -> L
  [(demonic FC) (λ (x) #t)]
  [(demonic (pred SV ℓ)) ;; MAYBE improve me: special case o?
   (λ f (x) (if (@ proc? x ★) 
                (@ f (@ x (-- (any/c)) ★) ★)  ;; want to add fact that x is a proc.
                (if (@ cons? x ★)
                    (amb (@ f (@ first x ★) ★)
                         (@ f (@ rest x ★) ★))
                    #t)))]  
  
  [(demonic (and/c C_0 C_1))
   (λ (x) (begin (@ (demonic C_0) x ★)
                 (@ (demonic C_1) x ★)))]
  
  [(demonic (cons/c C_0 C_1))
   (λ (x) (begin (@ (demonic C_0) (@ first x ★) ★)
                 (@ (demonic C_1) (@ rest x ★) ★)))]
  
  [(demonic (or/c C_0 C_1))
   (demonic (any/c))]  ;; Always safe, hard to do better.
   
  [(demonic (rec/c x C))
   (demonic (any/c))]  ;; Safe.  What else could you do?
  
  [(demonic (C_0 ... -> C_1)) 
   (λ (f) (@ (demonic C_1) (@ f (-- C_0) ... ★) ★))
   (where f ,(gensym 'f))])

;; Does o? hold on all values abstracted by V
;; [Gives an approximate answer: #f means "failed to prove"]
(define-metafunction λc~
  proves : V o? -> #t or #f
  [(proves (-- PV C ...) o?)
   #t
   (where #t (plain-δ o? PV Λ))]
  [(proves (-- C_0 ... C C_1 ...) o?) 
   #t
   (where #t (proves-con C o?))]
  [(proves V o?) #f])

(test
 (test-equal (term (proves (-- "Hi") string?)) #t))

;; Does (negate o?) hold on all values abstracted by AV
(define-metafunction λc~
  refutes : V o? -> #t or #f
  [(refutes (-- C_0 ... C C_1 ...) o?) 
   #t
   (where #t (refutes-con C o?))]
  [(refutes (-- PV C ...) o?)
   #t
   (where #f (plain-δ o? PV Λ))]   
  [(refutes V o?) #f])

(test
 (test-equal (term (refutes (-- 0) empty?)) #t))

;; Does satisfying C imply o?
(define-metafunction λc~
  proves-con : C o? -> #t or #f
  [(proves-con (pred o?_0 ℓ) o?_1) 
   (proves-predicate o?_0 o?_1)]
  [(proves-con (or/c C_0 C_1) o?)
   ,(and (term (proves-con C_0 o?))
         (term (proves-con C_1 o?)))]
  [(proves-con (and/c C_0 C_1) o?)
   ,(or (term (proves-con C_0 o?))
        (term (proves-con C_1 o?)))]
  [(proves-con (cons/c C_0 C_1) cons?) #t]
  [(proves-con (C_0 ... -> C_1) proc?) #t]
  [(proves-con C o?) #f])

(define-metafunction λc~
  proves-predicate : o? o? -> #t or #f
  [(proves-predicate o? o?) #t]
  [(proves-predicate zero? nat?) #t]
  [(proves-predicate false? bool?) #t]
  [(proves-predicate o?_0 o?_1) #f])

;; Does satisfying C imply (negate o?)
(define-metafunction λc~
  refutes-con : C o? -> #t or #f
  [(refutes-con (C_0 ... -> C_1) proc?) #f]
  [(refutes-con (C_0 ... -> C_1) o?) #t]
  [(refutes-con (pred o?_0 ℓ) o?_1) 
   (refutes-predicate o?_0 o?_1)]
  [(refutes-con (or/c C_0 C_1) o?)
   ,(and (term (refutes-con C_0 o?))
         (term (refutes-con C_1 o?)))]
  [(refutes-con (and/c C_0 C_1) o?)
   ,(or (term (refutes-con C_0 o?))
        (term (refutes-con C_1 o?)))]
  [(refutes-con (cons/c C_0 C_1) o?) 
   #t
   (side-condition (not (eq? (term o?) 'cons)))]
  [(refutes-con (rec/c x C) o?) 
   #f ;; FIXME
   #;(refutes-con (unroll (rec/c x C)) o?)]
  [(refutes-con C o?) #f])

(define-metafunction λc~
  refutes-predicate : o? o? -> #t or #f
  [(refutes-predicate o? o?) #f]
  [(refutes-predicate empty? o?) #t]
  [(refutes-predicate cons? o?) #t]
  [(refutes-predicate nat? zero?) #f]
  [(refutes-predicate zero? nat?) #f]
  [(refutes-predicate nat? o?) #t]
  [(refutes-predicate zero? o?) #t]
  [(refutes-predicate proc? o?) #t]
  [(refutes-predicate bool? false?) #f]
  [(refutes-predicate bool? o?) #t]
  [(refutes-predicate string? o?) #t]
  [(refutes-predicate false? bool?) #f]
  [(refutes-predicate false? o?) #t])
  

;; Totality tests
(test
 (redex-check λc~ (AV o?)
              (boolean? (term (proves AV o?))))
 (redex-check λc~ (AV o?)
              (boolean? (term (refutes AV o?))))
 (redex-check λc~ (C o?)
              (boolean? (term (proves-con C o?))))
 (redex-check λc~ (C_1 o?) ;; maybe restrict C_1 to valid?
              (boolean? (term (refutes-con C_1 o?)))))

  
;; Note: (proves-con C o?) and (refutes-con C o?) *both* hold
;; when C is inconsistent, e.g. (and/c nat? cons?).

(test
 (test-equal (term (proves-con (pred empty? ℓ) empty?)) #t)
 (test-equal (term (proves-con (pred cons? ℓ) empty?)) #f)
 (test-equal (term (proves-con (or/c (pred empty? ℓ)
                                     (pred cons? ℓ))
                               empty?))
             #f)
 (test-equal (term (proves-con (and/c (pred empty? ℓ)
                                      (pred cons? ℓ))
                               empty?))
             #t)
 (test-equal (term (proves-con ((pred empty? ℓ) -> (pred cons? ℓ))
                               empty?))
             #f)
 
 (test-equal (term (refutes-con (pred empty? ℓ) empty?)) #f)
 (test-equal (term (refutes-con (pred cons? ℓ) empty?)) #t)
 (test-equal (term (refutes-con (and/c (pred empty? ℓ)
                                       (pred cons? ℓ))
                                empty?))
             #t))             

;; Is C_1 /\ C_2 inhabited
(define-metafunction λc~
  feasible : C C -> #t or #f
  [(feasible FC (cons/c C_1 C_2)) #f]
  [(feasible (cons/c C_1 C_2) FC) #f]
  [(feasible FC (C_1 ... -> C_2)) #f]
  [(feasible (C_1 ... -> C_2) FC) #f]
  [(feasible (cons/c C_a C_b) (C_1 ... -> C_2)) #f]
  [(feasible (C_1 ... -> C_2) (cons/c C_a C_b)) #f]
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
(define-metafunction λc~
  domain-contracts : (C ...) -> (C ...)
  [(domain-contracts ()) ()]
  [(domain-contracts ((C_1 -> C_2) C ...))
   (C_1 C_0 ...)
   (where (C_0 ...) (domain-contracts (C ...)))]
  [(domain-contracts (C_0 C ...))
   (domain-contracts (C ...))])

;; All range contracts of all function contracts in given contracts.
(define-metafunction λc~
  range-contracts : (C ...) -> (C ...)
  [(range-contracts ()) ()]
  [(range-contracts ((C_1 ... -> C_2) C ...))
   (C_2 C_0 ...)
   (where (C_0 ...) (range-contracts (C ...)))]
  [(range-contracts (C_0 C ...)) 
   (range-contracts (C ...))])

(define-metafunction λc~
  ∧ : (C ...) -> C
  [(∧ ())  (any/c)]
  [(∧ (C)) C]
  [(∧ (C_0 C_1  ...))
   (and/c C_0 (∧ (C_1 ...)))])

(test
 (test-equal (term (∧ ())) (term (any/c)))
 (test-equal (term (∧ ((nat/c)))) (term (nat/c)))
 (test-equal (term (∧ ((nat/c) (string/c))))
             (term (and/c (nat/c) (string/c))))
 (test-equal (term (∧ ((nat/c) (string/c) (empty/c))))
             (term (and/c (nat/c) (and/c (string/c) (empty/c))))))
 
  
;; Does this value definitely pass this contract?
(define-metafunction λc~
  contract-in : C V -> #t or #f
  [(contract-in C (-- PV C_0 ... C C_1 ...)) #t]
  [(contract-in C (-- C_0 ... C C_1 ...)) #t]
  [(contract-in (pred (f ^ ℓ_0) ℓ_2) 
                (-- PV C_0 ... (pred (f ^ ℓ_1) ℓ_3) C_1 ...)) 
   #t]
  [(contract-in (pred (f ^ ℓ_0) ℓ_2) 
                (-- C_0 ... (pred (f ^ ℓ_1) ℓ_3) C_1 ...)) 
   #t]
  [(contract-in (pred o? ℓ) V)
   (proves V o?)]  
  [(contract-in C V) #f])

;; Does this abstract value *definitely* fail this contract?
;; FIXME do more here (or/c, rec/c, etc.)
(define-metafunction λc~
  contract-not-in : C V -> #t or #f  
  [(contract-not-in (pred o? ℓ) V)
   (refutes V o?)]
  [(contract-not-in FC V)
   #t
   (where #t (proves V proc?))]
  [(contract-not-in (and/c C_1 C_2) V)
   ,(or (term (contract-not-in C_1 V))
        (term (contract-not-in C_2 V)))]
  [(contract-not-in C V) #f])

;; Uncomment when contract-not-in is complete(r).
#;
(test 
 (test-equal (term (contract-not-in (rec/c x (or/c (pred empty? Λ) (cons/c (pred nat? Λ) x))) (-- 0)))
             #t))
      

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
  flat-check : (FLAT <= ℓ ℓ V-or-AE ℓ V) -> E
  [(flat-check (FLAT <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V))  
   (flat-check/defun FLAT V
                     (remember-contract V FLAT)
                     (blame ℓ_1 ℓ_3 V-or-AE FLAT V))])
  
;; the continuation ranges over: B | E.
(define-metafunction λc~
  meta-defun-apply : E C V -> E
  [(meta-defun-apply (blame ℓ_1 ℓ_2 V-or-AE C_0 V_0) C V)
   (blame ℓ_1 ℓ_2 V-or-AE C V)]
  [(meta-defun-apply E C V)
   E])

(define-metafunction λc~
  flat-check/defun : FLAT V E E_k -> E
  [(flat-check/defun anyc V E E_k) E]
  [(flat-check/defun C V E E_k)
   E 
   (where #t (contract-in C V))]
  [(flat-check/defun (and/c FLAT_0 FLAT_1) V E E_k)
   (flat-check/defun FLAT_0 V (flat-check/defun FLAT_1 V E E_k) E_k)]
  [(flat-check/defun C V E E_k)
   (meta-defun-apply E_k C V)
   (where #t (contract-not-in C V))]
  [(flat-check/defun (pred SV ℓ) V E E_k)
   (if (@ SV V ℓ) 
       E 
       (meta-defun-apply E_k (pred SV ℓ) V))]  
  [(flat-check/defun (cons/c FLAT_0 FLAT_1)
                     (-- (cons V_0 V_1) C ...)
                     E E_k)
   (flat-check/defun FLAT_0 V_0 (flat-check/defun FLAT_1 V_1 E E_k) E_k)]
  [(flat-check/defun (or/c FLAT_0 FLAT_1) V E E_k)
   (flat-check/defun FLAT_0 V
                   E
                   (flat-check/defun FLAT_1 V E 
                                     (meta-defun-apply E_k (or/c FLAT_0 FLAT_1) V)))]  
  [(flat-check/defun (rec/c x C) V E E_k)
   (flat-check/defun (unroll (rec/c x C)) V E E_k)]  
  [(flat-check/defun FLAT V E E_k) 
   (meta-defun-apply E_k FLAT V)])
 
(test
 (test-equal (term (proves (-- #t) bool?)) #t)
 (test-equal (term (flat-check ((and/c (pred nat? f) (pred empty? f)) <= f1 f2 (-- "V") f1 (-- #t))))
             (term (blame f1 f1 (-- "V") (pred nat? f) (-- #t))))
 (test-equal (term (flat-check/defun (string/c) (-- "Plain") #t #f)) #t)
 (test-equal (term (flat-check/defun (bool/c) (-- #t) #t #f)) #t)
 (test-equal (term (flat-check/defun (any/c) (-- 0) #t #f)) #t)
 (test-equal (term (flat-check/defun (cons/c (nat/c) (nat/c))
                                     (-- (cons (-- 0) (-- 1)))
                                     #t
                                     #f))
             #t)
 (test-equal (term (flat-check/defun (pred (λ (x) x) ℓ) (-- 0) #t #f))
             (term (if (@ (λ (x) x) (-- 0) ℓ)
                       #t
                       #f)))             
 ;; recursive contracts
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- 0) #t #f))
             #f)
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- empty) #t #f))
             #t)
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- (cons (-- 0) (-- empty))) #t #f))
             #t)
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- (cons (-- 0) (-- (cons (-- 0) (-- empty))))) #t #f))
             #t)
 (test-equal (term (flat-check/defun (rec/c x (or/c (empty/c) (cons/c (nat/c) x)))
                                     (-- (cons (-- "0") (-- empty))) #t #f))
             #f)
 
 (test-equal (term (flat-check ((cons/c (cons/c (nat/c) (nat/c)) (nat/c)) <= f1 f2 (-- 0) f1
                                                                    (-- (cons (-- (cons (-- "s") (-- "t"))) (-- "u"))))))
             (term (blame f1 f1 (-- 0) (nat/c) (-- "s"))))
 
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; δ

(define-metafunction λc~
  δ : (@ o V ... ℓ) -> (V-or-B V-or-B ...)
  [(δ (@ o (-- PV C ...) ... ℓ)) (wrap (plain-δ o PV ... ℓ))]
  [(δ (@ o V ... ℓ)) (abstract-δ o V ... ℓ)])

(define-metafunction λc~
  wrap : any -> (V-or-B)
  [(wrap PV) [(-- PV)]]
  [(wrap B) [B]]
  [(wrap V) [V]])

(define-metafunction λc~
  plain-δ : o PV ... ℓ -> V or PV or B  
  [(plain-δ string? string ℓ) #t]
  [(plain-δ string? PV ℓ) #f]
  [(plain-δ bool? bool ℓ) #t]
  [(plain-δ bool? PV ℓ) #f]
  [(plain-δ zero? 0 ℓ) #t]
  [(plain-δ zero? nat ℓ) #f]
  [(plain-δ proc? L ℓ) #t]
  [(plain-δ proc? PV ℓ) #f]
  [(plain-δ empty? empty ℓ) #t]
  [(plain-δ empty? PV ℓ) #f]
  [(plain-δ cons? (cons V_0 V_1) ℓ) #t]
  [(plain-δ cons? PV ℓ) #f]
  [(plain-δ nat? nat ℓ) #t]
  [(plain-δ nat? PV ℓ) #f]
  [(plain-δ false? #f ℓ) #t]
  [(plain-δ false? PV ℓ) #f]
  [(plain-δ add1 nat ℓ) ,(add1 (term nat))]
  [(plain-δ sub1 0 ℓ) 0]
  [(plain-δ sub1 nat ℓ) ,(sub1 (term nat))]
  [(plain-δ first (cons V_0 V_1) ℓ) V_0]
  [(plain-δ rest (cons V_0 V_1) ℓ) V_1]  
  [(plain-δ + nat_0 nat_1 ℓ) ,(+ (term nat_0) (term nat_1))]
  [(plain-δ - nat_0 nat_1 ℓ) ,(max 0 (- (term nat_0) (term nat_1)))]
  [(plain-δ * nat_0 nat_1 ℓ) ,(* (term nat_0) (term nat_1))]
  [(plain-δ expt nat_0 nat_1 ℓ) ,(expt (term nat_0) (term nat_1))]
  [(plain-δ = nat_0 nat_1 ℓ) ,(= (term nat_0) (term nat_1))]
  [(plain-δ < nat_0 nat_1 ℓ) ,(< (term nat_0) (term nat_1))]
  [(plain-δ <= nat_0 nat_1 ℓ) ,(<= (term nat_0) (term nat_1))]
  [(plain-δ > nat_0 nat_1 ℓ) ,(> (term nat_0) (term nat_1))]
  [(plain-δ >= nat_0 nat_1 ℓ) ,(>= (term nat_0) (term nat_1))]
  [(plain-δ cons PV_0 PV_1 ℓ) (cons (-- PV_0) (-- PV_1))]
  [(plain-δ o PV PV_0 ... ℓ)
   (blame ℓ o (-- PV) λ (-- PV))]) ;; FIXME: Not right value

(define-metafunction λc~
  impossible? : V -> #t or #f
  [(impossible? (-- PV C ...)) #f]
  [(impossible? (-- C))
   (impossible-con? C)]
  [(impossible? (-- C_0 C_1 C ...))
   ,(or (term (impossible? (-- C_0 C ...)))
        (term (impossible-con? C_1)))])

(define-metafunction λc~
  impossible-con? : C -> #t or #f
  [(impossible-con? C)   ;; Relies on theorem in lang:
   #t                    ;; WC! /\ FVC! = uninhabited
   (where WC! C)         ;; FIXME: Combine this with feasible
   (where FVC! C)]
  [(impossible-con? (or/c C_0 C_1))
   ,(and (term (impossible-con? C_0))
         (term (impossible-con? C_1)))]  
  [(impossible-con? (and/c C_0 C_1))
   ,(or (term (impossible-con? C_0))
        (term (impossible-con? C_1)))]
  [(impossible-con? (cons/c C_0 C_1))
   ,(or (term (impossible-con? C_0))
        (term (impossible-con? C_1)))]
  [(impossible-con? C) #f])

(define-metafunction λc~
  abstract-δ : o V ... ℓ -> (V-or-B V-or-B ...)
  [(abstract-δ o V_0 ... V V_1 ... ℓ)
   ((-- #f)) ;; V is impossible, so why not?
   (where #t (impossible? V))]
  
  ;; o?
  [(abstract-δ o? V ℓ) 
   ((-- #t) (-- #f))
   (where #t (proves V o?))
   (where #t (refutes V o?))]
  [(abstract-δ o? V ℓ) ((-- #t)) (where #t (proves V o?))]
  [(abstract-δ o? V ℓ) ((-- #f)) (where #t (refutes V o?))]
  [(abstract-δ o? V ℓ) 
   ((-- #t) (-- #f))]
  
  ;; nat->nat
  [(abstract-δ nat->nat V ℓ)
   ((-- (pred nat? Λ)))
   (where #t (proves V nat?))]
  [(abstract-δ nat->nat V ℓ)
   ((blame ℓ nat->nat V λ V))
   (where #t (refutes V nat?))]
  [(abstract-δ nat->nat V ℓ)
   ((-- (pred nat? Λ))
    (blame ℓ nat->nat V λ V))]
  
  ;; first
  [(abstract-δ first V ℓ)
   (proj-left V)
   (where #t (proves V cons?))]
  [(abstract-δ first V ℓ)
   ((blame ℓ first V λ V))
   (where #t (refutes V cons?))]
  [(abstract-δ first V ℓ)
   (V-or-B ... (blame ℓ first V λ V))
   (where (V-or-B ...) (proj-left V))]
  
  ;; rest
  [(abstract-δ rest V ℓ)
   (proj-right V)
   (where #t (proves V cons?))]
  [(abstract-δ rest V ℓ)
   ((blame ℓ rest V λ V) )
   (where #t (refutes V cons?))]
  [(abstract-δ rest V ℓ)
   (V-or-B ... (blame ℓ rest V λ V))
   (where (V-or-B ...) (proj-right V))]
  
  ;; nat*nat->nat
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((-- (nat/c)))
   (where #t (proves V_0 nat?))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((blame ℓ nat*nat->nat V_0 λ V_0))
   (where #t (refutes V_0 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((blame ℓ nat*nat->nat V_1 λ V_1))
   (where #t (refutes V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((-- (nat/c))
    (blame ℓ nat*nat->nat V_1 λ V_1))
   (where #t (proves V_0 nat?))]  
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((-- (nat/c))
    (blame ℓ nat*nat->nat V_0 λ V_0))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((-- (nat/c))
    (blame ℓ nat*nat->nat V_0 λ V_0)
    (blame ℓ nat*nat->nat V_1 λ V_1))]
  
  ;; nat*nat->bool
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((-- #t) (-- #f))
   (where #t (proves V_0 nat?))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((blame ℓ nat*nat->bool V_0 λ V_0))
   (where #t (refutes V_0 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((blame ℓ nat*nat->bool V_1 λ V_1))
   (where #t (refutes V_1 nat?))]    
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ nat*nat->bool V_1 λ V_1))
   (where #t (proves V_0 nat?))]  
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ nat*nat->bool V_0 λ V_0))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ nat*nat->bool V_0 λ V_0)
    (blame ℓ nat*nat->bool V_1 λ V_1))]
  
  ;; cons
  [(abstract-δ cons V_0 V_1 ℓ)
   ((-- (cons V_0 V_1)))])

;; Project an AV to the left
;; (proj-left (-- (cons/c nat? string?) (cons/c zero? string?)))
;; ≡ (-- nat? zero?)
(define-metafunction λc~
  proj-left : AV -> (V ...)
  [(proj-left (-- C_0 C ...))
   (proj-left/a ((-- (any/c))) C_0 C ...)])

(define-metafunction λc~
  proj-right : AV -> (V ...)
  [(proj-right (-- C_0 C ...))
   (proj-right/a ((-- (any/c))) C_0 C ...)])

(define-metafunction λc~
  proj-left/a : ((-- C ...) ...) C ... -> (V ...)
  [(proj-left/a (AV ...)) (AV ...)]  
  [(proj-left/a (AV ...) (cons/c C_0 C_1) C_2 ...)
   (proj-left/a (AV_R ...) C_2 ...)
   (where (AV_R ...) 
          ,(for*/list ([av (in-list (term (AV ...)))]
                       [cnew (in-list (term (explode C_0)))])
             (term (remember-contract ,av ,cnew))))]
  [(proj-left/a (AV ...) C_0 C_1 ...)
   (proj-left/a (AV ...) C_1 ...)])

(define-metafunction λc~
  proj-right/a : ((-- C ...) ...) C ... -> (V ...)
  [(proj-right/a (AV ...)) (AV ...)]  
  [(proj-right/a (AV ...) (cons/c C_0 C_1) C_2 ...)
   (proj-right/a (AV_R ...) C_2 ...)
   (where (AV_R ...) 
          ,(for*/list ([av (in-list (term (AV ...)))]
                       [cnew (in-list (term (explode C_1)))])
             (term (remember-contract ,av ,cnew))))]
  [(proj-right/a (AV ...) C_0 C_1 ...)
   (proj-right/a (AV ...) C_1 ...)])

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
 (test-equal (term (δ (@ proc? (-- ((any/c) -> (any/c))) †)))
             (term ((-- #t))))
 
 (test-equal (term (δ (@ cons (-- 1) (-- 2) †)))
             (term ((-- (cons (-- 1) (-- 2))))))
 
 (test-equal (term (δ (@ proc? (-- (nat/c)) ★)))
             (term ((-- #f))))
 
 (test-equal (term (δ (@ rest (-- (cons/c (any/c) (any/c))) f))) 
             (term ((-- (any/c)))))
 (test-equal (term (δ (@ rest (-- (cons/c (any/c) (or/c (nat/c) (string/c)))) f)))
             (term ((-- (nat/c)) (-- (string/c)))))
 
 (test-equal (term (explode (or/c (nat/c) (string/c))))
             (term ((nat/c) (string/c))))
 
 (test-equal (term (proj-right (-- (cons/c (any/c) (or/c (nat/c) (string/c))))))
             (term ((-- (nat/c)) (-- (string/c)))))
 
 (test-equal (term (refutes (-- (nat/c)) proc?))
             #t)
             
 (test-equal (term (refutes-con (nat/c) proc?))
             #t)
 
 (redex-check λc~ WFV (term (∈ #f (δ (@ proc? WFV ℓ)))))
 
 ;; Test for δ totalness.
 (redex-check λc~ (o1 V) (or (not (term (valid-value? V)))
                             (term (δ (@ o1 V f)))))
 (redex-check λc~ (o2 V_1 V_2) (or (not (term (valid-value? V_1)))
                                   (not (term (valid-value? V_2)))
                                   (term (δ (@ o2 V_1 V_2 f))))))