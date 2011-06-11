#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "name.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test meta)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metafunctions

(define-metafunction λc~
  demonic : C -> L
  [(demonic any/c)
   (λ f x (if (@ proc? x ★) 
              (@ f (@ x (-- any/c) ★) ★)  ;; want to add fact that x is a proc.
              0))]
  [(demonic (pred SV ℓ))
   (demonic any/c)]
  [(demonic nat/c) (λ x 0)]
  [(demonic string/c) (λ x 0)]
  [(demonic bool/c) (λ x 0)]
  [(demonic none/c) (λ x 0)]
  ;; Maybe add blessed arrow contracts
  [(demonic (C_0 -> C_1)) 
   (λ f (@ (demonic C_1) (@ f (-- C_0) ★) ★))
   (where f ,(gensym 'f))])

;; Does o? hold on all values abstracted by AV
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

;; Does (negate o?) hold on all values abstracted by AV
(define-metafunction λc~
  refutes : V o? -> #t or #f
  [(refutes (-- C_0 ... C C_1 ...) o?) 
   #t
   (where #t (refutes-con C o?))]
  [(refutes V o?) #f])

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
  [(proves-con (C_0 -> C_1) proc?) #t]
  [(proves-con nat/c nat?) #t]
  [(proves-con C o?) #f])

(define-metafunction λc~
  proves-predicate : o? o? -> #t or #f
  [(proves-predicate o? o?) #t]
  [(proves-predicate zero? nat?) #t]
  [(proves-predicate o?_0 o?_1) #f])

;; Does satisfying C imply (negate o?)
(define-metafunction λc~
  refutes-con : C o? -> #t or #f
  [(refutes-con (C_0 -> C_1) proc?) #f]
  [(refutes-con (C_0 -> C_1) o?) #t]
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
  [(refutes-con FC proc?) #t]
  [(refutes-con (flat-rec/c x C)) #f] ;; fixme
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
  [(refutes-predicate proc? o?) #t])

;; Totality tests
(test
 (redex-check λc~ (AV o?)
              (boolean? (term (proves AV o?))))
 (redex-check λc~ (AV o?)
              (boolean? (term (refutes AV o?))))
 (redex-check λc~ (C o?)
              (boolean? (term (proves-con C o?))))
 (redex-check λc~ (C o?)
              (boolean? (term (refutes-con C o?)))))

  
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remember-contract

(define-metafunction λc~
  remember-contract : V C ... -> V
  [(remember-contract V) V]
  ;; Expand away and/c
  [(remember-contract V (and/c C_1 C_2) C ...)
   (remember-contract V C_1 C_2 C ...)]
  ;; drop boring contracts on concrete flat values
  [(remember-contract (-- FV C_1 ...) C_0 C ...)
   (remember-contract (-- FV C_1 ...) C ...)
   (side-condition (not (redex-match λc~ FC (term C_0))))]
  ;; drop any/c on the floor when possible
  [(remember-contract (-- any/c C C_1 ...) C_2 ...)
   (remember-contract (-- C C_1 ...) C_2 ...)]
  [(remember-contract (-- any/c) C C_2 ...)
   (remember-contract (-- C) C_2 ...)]
  [(remember-contract V any/c C_2 ...)
   (remember-contract V C_2 ...)]
  ;; do the real work
  [(remember-contract (-- any_0 C_0 ... C C_1 ...) C C_2 ...)
   (remember-contract (-- any_0 C_0 ... C C_1 ...) C_2 ...)]
  [(remember-contract (-- any_0 C_1 ...) C_2 C ...)
   (remember-contract (-- any_0 C_1 ... C_2) C ...)])

(test
 ;; check that remember-contract is total and produces the right type
 (redex-check λc~ (V C ...)              
              (redex-match λc~ V (term (remember-contract V C ...)))))
             

;; If f refers to a module contract with an arrow contract, get 
;; domain contract; otherwise, any/c.
(define-metafunction λc~
  dom-contract : f (M ...) -> C
  [(dom-contract f (any_0 ... (module f (C_0 -> C_1) any) any_1 ...))
   C_0]
  [(dom-contract f any) any/c])

(define-metafunction λc~
  strip-concrete-contracts : V -> AV or PV
  [(strip-concrete-contracts (-- PV C ...)) PV]
  [(strip-concrete-contracts AV) AV])

;; All range contracts of all function contracts in given contracts.
(define-metafunction λc~
  range-contracts : (C ...) -> (C ...)
  [(range-contracts ()) ()]
  [(range-contracts ((C_1 -> C_2) C ...))
   (C_2 C_0 ...)
   (where (C_0 ...) (range-contracts (C ...)))]
  [(range-contracts (C_0 C ...)) (range-contracts (C ...))])
  
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
  [(contract-in C V) #f])

;; Does this abstract value *definitely* fail this contract?
(define-metafunction λc~
  contract-not-in : C AV -> #t or #f  
  [(contract-not-in FC_1 (-- C_0 ... FC_2 C_1 ...)) #t
   (side-condition (not (eq? (term FC_1) (term FC_2))))]
  [(contract-not-in FC_1 (-- C_0 ... (C_a -> C_b) C_1 ...)) #t]
  [(contract-not-in C AV) #f])

;; FIXME returns first domain, should return most specific.
(define-metafunction λc~
  most-specific-domain : C ... -> C
  [(most-specific-domain (C_1 -> C_2) C ...) C_1]
  [(most-specific-domain C ...) any/c])

;; Removes duplicate remembered contracts.
(define-metafunction λc~
  normalize : V -> V
  [(normalize (-- PV C ...)) (-- PV C_1 ...)
   (where (C_1 ...)
          ,(remove-duplicates (term (C ...))
                              (match-lambda**
                               [(`(,f ^ _) `(,f ^ _)) #t]
                               [(a b) (equal? a b)])))]
  [(normalize (-- C ...)) (-- C_1 ...)
   (where (C_1 ...)
          ,(remove-duplicates (term (C ...))
                              (match-lambda**
                               [(`(,f ^ _) `(,f ^ _)) #t]
                               [(a b) (equal? a b)])))])

(test
 (redex-check λc~ V  (redex-match λc~ V (term (normalize V)))))


(define-metafunction λc~
  flat-check : FLAT V E any -> E
  [(flat-check any/c V E any) E]
  [(flat-check none/c V E any) 
   (meta-apply any none/c V)]
  [(flat-check C V E any)
   E 
   (where #t (contract-in C V))]
  [(flat-check C AV E any)
   (meta-apply any C AV)
   (where #t (contract-not-in C AV))]
  [(flat-check (pred SV ℓ) V E any)
   (if (@ SV V ℓ) 
       E 
       (meta-apply any (pred SV ℓ) V))]
  [(flat-check (cons/c FLAT_0 FLAT_1)
               (-- (cons V_0 V_1) C ...)
               E any)
   (flat-check FLAT_0
               V_0
               (flat-check FLAT_1 V_1 E 
                           ,(λ (f v) (term (meta-apply any FLAT_1 V_1))))
               ,(λ (f v) (term (meta-apply any FLAT_0 V_0))))]
  [(flat-check (cons/c C_0 C_1) V E any) 
   (meta-apply any (cons/c C_0 C_1) V)]
  
  [(flat-check (or/c FLAT_0 FLAT_1) V E any)
   (flat-check FLAT_0 V
               E
               ,(λ (f v) (term (flat-check FLAT_1 V E 
                                           ,(λ (f v) (term (meta-apply any FLAT_1 V)))))))]
  [(flat-check (and/c FLAT_0 FLAT_1) V E any)
   (flat-check FLAT_0 V
               (flat-check FLAT_1 V E ,(λ (f v) (term (meta-apply any FLAT_1 V))))
               ,(λ (f v) (term (meta-apply any FLAT_0 V))))]

  ;; FIXME: Rewrite with proves.
  [(flat-check nat/c anat E any) E]
  [(flat-check nat/c (-- C_1 ... (pred nat? any_l) C_2 ...) E any) E]
  [(flat-check string/c astring E any) E]
  [(flat-check bool/c abool E any) E]
  [(flat-check empty/c aempty E any) E]
  
  [(flat-check (flat-rec/c x C) V E any)
   (flat-check (subst x (flat-rec/c x C) C) V E any)]
  
  [(flat-check FLAT V E any) 
   (meta-apply any FLAT V)
   (side-condition (procedure? (term any)))])

(define-metafunction λc~
  meta-apply : any any ... -> any
  [(meta-apply any_f any ...)
   ,(apply (term any_f) (term (any ...)))])

(test
 (test-equal (term (flat-check none/c (-- 0) #t ,(λ (f v) #f))) #f)
 (test-equal (term (flat-check any/c (-- 0) #t ,(λ (f v) #f))) #t)
 (test-equal (term (flat-check (cons/c nat/c nat/c)
                               (-- (cons (-- 0) (-- 1)))
                               #t
                               ,(λ (f v) #f)))
             #t)
 (test-equal (term (flat-check (and/c nat/c none/c) (-- 0) #t ,(λ (f v) #f)))
             #f)
 (test-equal (term (flat-check (and/c none/c nat/c) (-- 0) #t ,(λ (f v) #f)))
             #f)
 (test-equal (term (flat-check (or/c nat/c none/c) (-- 0) #t ,(λ (f v) #f)))
             #t)
 (test-equal (term (flat-check (or/c none/c nat/c) (-- 0) #t ,(λ (f v) #f)))
             #t)
 (test-equal (term (flat-check (pred (λ x x) ℓ) (-- 0) #t ,(λ (f v) #f)))
             (term (if (@ (λ x x) (-- 0) ℓ)
                       #t
                       #f)))
 ;; recursive contracts
 (test-equal (term (flat-check (flat-rec/c x (or/c empty/c (cons/c nat/c x)))
                               (-- 0) #t ,(λ (f v) #f)))
             #f)
 (test-equal (term (flat-check (flat-rec/c x (or/c empty/c (cons/c nat/c x)))
                               (-- empty) #t ,(λ (f v) #f)))
             #t)
 (test-equal (term (flat-check (flat-rec/c x (or/c empty/c (cons/c nat/c x)))
                               (-- (cons (-- 0) (-- empty))) #t ,(λ (f v) #f)))
             #t)
 (test-equal (term (flat-check (flat-rec/c x (or/c empty/c (cons/c nat/c x)))
                               (-- (cons (-- 0) (-- (cons (-- 0) (-- empty))))) #t ,(λ (f v) #f)))
             #t)
 (test-equal (term (flat-check (flat-rec/c x (or/c empty/c (cons/c nat/c x)))
                               (-- (cons (-- "0") (-- empty))) #t ,(λ (f v) #f)))
             #f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; δ

(define-metafunction λc~
  δ : (@ o V ... ℓ) -> V or B or (if (-- bool/c) E E)
  [(δ (@ o (-- PV C ...) ... ℓ)) (wrap (plain-δ o PV ... ℓ))]
  [(δ (@ o V ... ℓ))  (wrap (abstract-δ o V ... ℓ))])

(define-metafunction λc~
  wrap : any -> E
  [(wrap PV) (-- PV)]
  [(wrap E) E])

(define-metafunction λc~
  plain-δ : o PV ... ℓ -> V or PV or B  
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
  [(impossible? CV) #f]
  [(impossible? (-- C))
   (impossible-con? C)]
  [(impossible? (-- C_0 C_1 C ...))
   ,(or (term (impossible? (-- C_0 C ...)))
        (term (impossible-con? C_1)))])

(define-metafunction λc~
  impossible-con? : C -> #t or #f
  [(impossible-con? none/c) #t]
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
  abstract-δ : o V ... ℓ -> PV or V or B or (if (-- bool/c) E E)
  [(abstract-δ o V_0 ... V V_1 ... ℓ)
   (-- none/c)
   (where #t (impossible? V))]
  ;; o?
  [(abstract-δ o? V ℓ) #t (where #t (proves V o?))]
  [(abstract-δ o? V ℓ) #f (where #t (refutes V o?))]
  [(abstract-δ o? V ℓ) (-- bool/c)]
  
  ;; nat->nat
  [(abstract-δ nat->nat V ℓ)
   (-- (pred nat? Λ))
   (where #t (proves V nat?))]
  [(abstract-δ nat->nat V ℓ)
   (blame ℓ nat->nat V λ V)
   (where #t (refutes V nat?))]
  [(abstract-δ nat->nat V ℓ)
   (if (-- bool/c)
       (-- (pred nat? Λ))
       (blame ℓ nat->nat V λ V))]
  
  ;; first
  [(abstract-δ first V ℓ)
   (proj-left V)
   (where #t (proves V cons?))]
  [(abstract-δ first V ℓ)
   (blame ℓ first V λ V) 
   (where #t (refutes V cons?))]
  [(abstract-δ first V ℓ)
   (if (-- bool/c)
       (proj-left V)
       (blame ℓ first V λ V))]
  
  ;; rest
  [(abstract-δ rest V ℓ)
   (proj-right V)
   (where #t (proves V cons?))]
  [(abstract-δ rest V ℓ)
   (blame ℓ rest V λ V) 
   (where #t (refutes V cons?))]
  [(abstract-δ rest V ℓ)
   (if (-- bool/c)
       (proj-right V)
       (blame ℓ rest V λ V))]
  
  ;; nat*nat->nat
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   (-- nat/c)
   (where #t (proves V_0 nat?))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   (blame ℓ nat*nat->nat V_0 λ V_0)   
   (where #t (refutes V_0 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   (blame ℓ nat*nat->nat V_1 λ V_1)   
   (where #t (refutes V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   (if (-- bool/c)
       (-- nat/c)
       (blame ℓ nat*nat->nat V_1 λ V_1))
   (where #t (proves V_0 nat?))]  
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   (if (-- bool/c)
       (-- nat/c)
       (blame ℓ nat*nat->nat V_0 λ V_0))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   (if (-- bool/c)
       (-- nat/c)
       (if (-- bool/c)
           (blame ℓ nat*nat->nat V_0 λ V_0)
           (blame ℓ nat*nat->nat V_1 λ V_1)))]
  
  ;; nat*nat->bool
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   (-- bool/c)
   (where #t (proves V_0 nat?))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   (blame ℓ nat*nat->bool V_0 λ V_0)   
   (where #t (refutes V_0 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   (blame ℓ nat*nat->bool V_1 λ V_1)   
   (where #t (refutes V_1 nat?))]    
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   (if (-- bool/c)
       (-- bool/c)
       (blame ℓ nat*nat->bool V_1 λ V_1))
   (where #t (proves V_0 nat?))]  
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   (if (-- bool/c)
       (-- bool/c)
       (blame ℓ nat*nat->bool V_0 λ V_0))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   (if (-- bool/c)
       (-- bool/c)
       (if (-- bool/c)
           (blame ℓ nat*nat->bool V_0 λ V_0)
           (blame ℓ nat*nat->bool V_1 λ V_1)))]
  
  ;; cons
  [(abstract-δ cons V_0 V_1 ℓ)
   (-- (cons V_0 V_1))])

;; Project an AV to the left
;; (proj-left (-- (cons/c nat? string?) (cons/c zero? string?)))
;; ≡ (-- nat? zero?)
(define-metafunction λc~
  proj-left : AV -> AV
  [(proj-left (-- C_0 C ...))
   (proj-left/a (-- any/c) C_0 C ...)])

(define-metafunction λc~
  proj-right : AV -> AV
  [(proj-right (-- C_0 C ...))
   (proj-right/a (-- any/c) C_0 C ...)])

(define-metafunction λc~
  proj-left/a : (-- C ...) C ... -> AV
  [(proj-left/a AV) AV]
  [(proj-left/a (-- C ...) (cons/c C_0 C_1) C_2 ...)
   (proj-left/a (remember-contract (-- C ...) C_0) C_2 ...)]
  [(proj-left/a (-- C ...) C_0 C_1 ...)
   (proj-left/a (-- C ...) C_1 ...)])

(define-metafunction λc~
  proj-right/a : (-- C ...) C ... -> AV
  [(proj-right/a AV) AV]
  [(proj-right/a (-- C ...) (cons/c C_0 C_1) C_2 ...)
   (proj-right/a (remember-contract (-- C ...) C_1) C_2 ...)]
  [(proj-right/a (-- C ...) C_0 C_1 ...)
   (proj-right/a (-- C ...) C_1 ...)])

(test 
 (test-equal (term (δ (@ proc? (-- (any/c -> any/c)) †)))
             (term (-- #t)))
 
 (test-equal (term (δ (@ cons (-- 1) (-- 2) †)))
             (term (-- (cons (-- 1) (-- 2)))))
 
 (test-equal (term (δ (@ proc? (-- nat/c) ★)))
             (term (-- #f)))
 
 (test-equal (term (refutes (-- nat/c) proc?))
             #t)
             
 (test-equal (term (refutes-con nat/c proc?))
             #t)
 
 ;; Test for δ totalness.
 (redex-check λc~ (o1 V) (term (δ (@ o1 V f))))
 (redex-check λc~ (o2 V_1 V_2) (term (δ (@ o2 V_1 V_2 f)))))