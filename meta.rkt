#lang racket
(require redex/reduction-semantics)
(require "lang.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metafunctions

(define-metafunction λc~
  demonic : C -> L
  [(demonic any/c)
   (λ f x (if (proc? x ★) 
              (f (x (-- any/c) ★) ★)  ;; want to add fact that x is a proc.
              0))]
  [(demonic (pred SV))
   (demonic any/c)]
  [(demonic int/c) (λ x 0)]
  [(demonic string/c) (λ x 0)]
  [(demonic bool/c) (λ x 0)]
  [(demonic none/c) (λ x 0)]
  ;; Maybe add blessed arrow contracts
  [(demonic (C_0 -> C_1)) 
   (λ f ((demonic C_1) (f (-- C_0) ★) ★))
   (where f ,(gensym 'f))])

;; FIXME: Don't handle abstract values
(define-metafunction λc~
  prim-δ : (o V ... f) -> AV or PV or B
  [(prim-δ (add1 (-- n C ...) f)) ,(add1 (term n))]
  [(prim-δ (sub1 (-- 0 C ...) f)) 0]
  [(prim-δ (sub1 (-- n C ...) f)) ,(sub1 (term n))]
  [(prim-δ (zero? (-- n C ...) f)) ,(zero? (term n))]  
  [(prim-δ (+ (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(+ (term n_1) (term n_2))]
  [(prim-δ (- (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(max 0 (- (term n_1) (term n_2)))]
  [(prim-δ (* (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(* (term n_1) (term n_2))]
  [(prim-δ (expt  (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(expt (term n_1) (term n_2))]
  [(prim-δ (= (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(= (term n_1) (term n_2))]
  [(prim-δ (< (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(< (term n_1) (term n_2))]
  [(prim-δ (<= (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(<= (term n_1) (term n_2))]
  [(prim-δ (> (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(> (term n_1) (term n_2))]  
  [(prim-δ (>= (-- n_1 C_0 ...) (-- n_2 C_1 ...) f)) ,(>= (term n_1) (term n_2))]

  [(prim-δ (proc? W f)) #t]
  [(prim-δ (proc? WFV f)) #f]
  [(prim-δ (proc? W? f)) (-- bool/c)]
  
  [(prim-δ (o1 V f)) (blame f o1 V λ V)]
  ;; FIXME: should refer to V_1 and V_2.
  [(prim-δ (o2 V_1 V_2 f)) (blame f o2 V_1 λ V_1)])

(test-equal (term (prim-δ (proc? (-- #f) f))) #f)
(test-equal (term (prim-δ (add1 (-- 0) f))) 1)
(test-equal (term (prim-δ (sub1 (-- 0) f))) 0)
(test-equal (term (prim-δ (zero? (-- 0) f))) #t)
(test-equal (term (prim-δ (zero? (-- 1) f))) #f)
(test-equal (term (prim-δ (add1 (-- #t) f))) (term (blame f add1 (-- #t) λ (-- #t))))

(define-metafunction λc~
  wrap-δ : any -> V or B
  [(wrap-δ AV) AV]
  [(wrap-δ PV) (-- PV)]
  [(wrap-δ B) B])

(define-metafunction λc~
  δ : (o V ... f) -> V or B
  [(δ (o V ... f)) (wrap-δ (prim-δ (o V ... f)))])

(test-equal (term (δ (proc? (-- (any/c -> any/c)) †)))
            (term (-- #t)))

;; Test for δ totalness.
(redex-check λc~ (o1 V)
             (or (redex-match λc~ V (term (δ (o1 V f))))
                 (equal? (term (blame f o1 V λ V))
                         (term (prim-δ (o1 V f))))))
(redex-check λc~ (o2 V_1 V_2)
             (or (redex-match λc~ V (term (δ (o2 V_1 V_2 f))))
                 (redex-match λc~ B (term (δ (o2 V_1 V_2 f))))))

(define-metafunction λc~ subst : x any any -> any  
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

(test-equal (term (subst x 0 x)) (term 0))
(test-equal (term (subst x 0 y)) (term y))
(test-equal (term (subst x 0 (λ x x))) (term (λ x x)))

(define-metafunction λc~
  remember-contract : V C ... -> V
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
  [(remember-contract (-- any_0 C_1 ...) C_2 ...)
   (-- any_0 C_2 ... C_1 ...)]
  ;; descend inside blessed arrow contracts
  [(remember-contract ((C_1 --> C_2) <= f_1 f_2 V_1 f_3 V_2) C ...)
   ((C_1 --> C_2) <= f_1 f_2 V_1 f_3 (remember-contract V_2 C ...))])

;; check that remember-contract is total and produces the right type
(redex-check λc~ (V C ...)              
             (redex-match λc~ V (term (remember-contract V C ...))))

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

;; Given a flat contract and plain value, checks satisfaction.
(define-metafunction λc~
  flat-pass : FC PV -> #t or #f
  [(flat-pass int/c int) #t]
  [(flat-pass string/c string) #t]
  [(flat-pass bool/c bool) #t]
  [(flat-pass FC PV) #f])

;; Totality check
(redex-check λc~ (FC PV) (boolean? (term (flat-pass FC PV))))

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
  [(contract-in (pred (f_a ^ f_b)) (-- PV C_0 ... (pred (f_a ^ f_c)) C_1 ...)) #t]
  [(contract-in (pred (f_a ^ f_b)) (-- C_0 ... (pred (f_a ^ f_c)) C_1 ...)) #t]
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
  [(normalize ((C_1 --> C_2) <= f_1 f_2 V_1 f_3 V)) (normalize V)]
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

(redex-check λc~ V  (redex-match λc~ V (term (normalize V))))


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

(test-equal (term (≡α (λ x x) (λ y y))) #t)
(test-equal (term (≡α (λ x x) (λ y z))) #f)
(test-equal (term (≡α 3 3)) #t)
(test-equal (term (≡α 3 4)) #f)
(test-equal (term (≡α ((λ x x) 3 f) ((λ y y) 3 f))) #t)
(test-equal (term (≡α ((λ x x) (λ y y) f) ((λ y y) (λ x x) f))) #t)

(redex-check λc~ E (term (≡α E E)))











































