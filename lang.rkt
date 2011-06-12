#lang racket
(require redex "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test lang)
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Languages

;; Figure 5.
(define-language λc-user
  
  ;; Annotated language
  (P (M ... E))
  (M (module f C PV))
  (L (λ x E) (λ x x E))
  (W (-- L C* ...))
  (bool #t #f)
  ;; Plain value
  (PV FV L)
  
  ;; A flat value is definitely not a procedure
  (FV nat bool string empty (cons V V))
  
  (V-or-x V x)
  
  ;; Values
  (V WFV W)
  
  (WFV (-- FV C* ...))
  
  (SV L (f ^ f) o1) ; Syntactic values for pred.
  (E V PV x (f ^ ℓ) (@ E E ℓ) (if E E E) (@ o1 E ℓ) (@ o2 E E ℓ) (let x E E) (begin E E))
  
  (FLAT FC any/c
        (pred SV ℓ)
        (cons/c FLAT FLAT)
        (or/c FLAT FLAT)
        (rec/c x FLAT) x
        (and/c FLAT FLAT))
  (HOC (C -> C)
       (or/c FLAT HOC)
       (cons/c HOC C) (cons/c C HOC)
       (and/c HOC C)  (and/c C HOC)
       (rec/c x HOC) x)
  
  
  (FLAT* FC any/c  (pred SV ℓ) (cons/c FLAT FLAT) (or/c FLAT FLAT) (rec/c x FLAT))
  (HOC* (C -> C)
        (or/c FLAT HOC)
        (cons/c HOC C) (cons/c C HOC)
        (rec/c x HOC))
     
  (FC nat/c bool/c string/c empty/c)
  (C* FLAT* HOC*)  
  (C FLAT HOC)
  
  (x variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned)
  (ℓ f o † ★ Λ) ;; † is top-level, ★ is demonic generated, Λ is language generated
  (nat natural)
  (o o1 o2)
  (o1 o? nat->nat first rest)
  (nat->nat add1 sub1)
  ;; Built-in predicates
  (o? zero? proc? empty? cons? nat? string?)
  (o2 nat*nat->nat nat*nat->bool cons)
  (nat*nat->nat + - * expt)
  (nat*nat->bool = < <= > >=)
  
  (𝓔 hole (@ 𝓔 E ℓ) (@ V 𝓔 ℓ) (if 𝓔 E E) (@ o V ... 𝓔 E ... ℓ) (let x 𝓔 E) (begin 𝓔 E)))

;; Figure 5, gray (cont).
(define-extended-language λc λc-user
  (B (blame ℓ ℓ V C V))
  (E .... (C <= ℓ ℓ V-or-x ℓ E) B)
  (𝓔 .... (C <= ℓ ℓ V ℓ 𝓔)))

;; Figure 5, gray (cont).
(define-extended-language λc~ λc
  (AE (-- C* C* ...))      ;; Abstract expressions
  (AV (-- C*-top C* ...))  ;; Abstract values
  (CV (-- PV C* ...))      ;; Concrete values
  (C-ext C λ)
      
  (V-or-AE V AE)
  (E .... AE (C <= ℓ ℓ AE ℓ E))
  (𝓔 .... (C <= ℓ ℓ AE ℓ 𝓔))
  (B ....
     (blame ℓ ℓ AE C V) 
     (blame ℓ ℓ V λ V)) ;; broke the contract with the language
  
  (WFV .... 
       (-- C*-top C* ... FVC!* C* ...)
       (-- FVC!*-top C* ...))
  
  ;; Representations of abstract values
  ;; no or/c or rec/c at top-level
  (C*-top FC 
          any/c 
          (pred SV ℓ)
          (C -> C)
          (cons/c C C))
  
  ;; Definite flat value contract
  ;; Contract variables are not needed: to be productive,
  ;; contract variables must occur with C occurrences.
  
  (FLAT-FVC! (side-condition FVC!_1 (redex-match λc~ FLAT (term FVC!_1))))
  
  (FVC! FVC!*
        (and/c C FVC!)
        (and/c FVC! C))
  (FVC!* FVC!*-top
         (or/c FLAT-FVC! FVC!)         
         (rec/c x FVC!))
  (FVC!*-top FC (cons/c C C))
  
  (V .... AV)             ;; (-- X) is overline X.
  (M .... (module f C ☁))

  ;; Definite procedure contract
  (WC! WC!* (and/c C WC!) (and/c WC! C))
  (WC!* WC!*-top (rec/c x WC!))
  (WC!*-top (C -> C) (pred proc? ℓ))
  
  ;; Definite procedure  
  (W .... 
     (-- C*-top C* ... WC!* C* ...)
     (-- WC!*-top C* ...))
  
    
  ;; Note: uninhabited contracts may be both definitely flat and procedures.
  
  ;; Maybe procedure contract
  (WC? WC?* (and/c WC? WC?))  
  (WC?* WC?*-top
        (or/c WC? C)
        (or/c C WC?)       
        (or/c FVC! WC!)
        (or/c WC! FVC!)       
        (rec/c x WC?))  
  (WC?*-top any/c
            (pred (side-condition SV_1 (not (equal? (term SV_1) 'proc?))) ℓ))

  ;; Maybe procedure
  (W? W 
      (-- C*-top C* ... WC?* C* ...)
      (-- WC?*-top C* ...))
  
  ;; Raw, unannotated language
  (RP (RM ... RE))
  (RM (module f RC RPV) (module f RC ☁))
  (RL (λ x RE) (λ x x RE))
  (RPV FV RL)  
  (RSV RL f o1) ; Syntactic values for pred.
  (RE RPV x f (RE RE) (if RE RE RE) (o1 RE) (o2 RE RE) (let x RE RE) (begin RE RE))
  
  
  (RCFLAT FC any/c  (pred RSV) (cons/c RCFLAT RCFLAT) (or/c RCFLAT RCFLAT) (and/c RCFLAT RCFLAT)
          (rec/c x RCFLAT) x)
  (RCHOC (RC -> RC)
         (or/c RCFLAT RCHOC)
         (cons/c RCHOC RC) (cons/c RC RCHOC)
         (and/c RCHOC RC)  (and/c RC RCHOC)
         (rec/c x RCHOC))
  
  (RC RCFLAT RCHOC))
  

(define-metafunction λc~
  productive? : C x ... -> #t or #f
  [(productive? x x_0 ... x x_1 ...) #f]
  [(productive? x x_0 ...) #t]
  [(productive? (rec/c x C) x_0 ...)
   (productive? C x x_0 ...)]
  [(productive? (cons/c C_1 C_2) x_0 ...)
   ,(and (term (productive? C_1))
         (term (productive? C_2)))]
  [(productive? (C_1 -> C_2) x_0 ...)
   ,(and (term (productive? C_1))
         (term (productive? C_2)))]
  [(productive? (or/c C_1 C_2) x_0 ...)
   ,(and (term (productive? C_1 x_0 ...))
         (term (productive? C_2 x_0 ...)))]
  [(productive? (and/c C_1 C_2) x_0 ...)
   ,(and (term (productive? C_1 x_0 ...))
         (term (productive? C_2 x_0 ...)))]
  [(productive? C x ...) #t])

(test
 (test-equal (term (productive? any/c)) #t)
 (test-equal (term (productive? (rec/c x x))) #f)
 (test-equal (term (productive? (or/c any/c (rec/c x x)))) #f)
 (test-equal (term (productive? (rec/c x (or/c empty/c (cons/c any/c x))))) #t)
 (test-equal (term (productive? (any/c -> any/c))) #t)
 (test-equal (term (productive? (or/c (rec/c a a) (any/c -> any/c)))) #f))

(test
 (test-equal (redex-match λc~ AV (term (-- any/c (and/c nat/c nat/c))))
             #f))

(define abstract-value? (redex-match λc~ (-- C* ...)))
(define (final-state? x)
  (or (redex-match λc~ V x)
      (redex-match λc~ B x)
      (redex-match λc~ (-- C_0 ...  C_1 ...))))

(define-metafunction λc~
  FV/C : C -> (x ...)
  [(FV/C x) (x)]
  [(FV/C (rec/c x C))
   (set-minus (FV/C C) x)]
  [(FV/C (cons/c C_1 C_2))
   ,(append (term (FV/C C_1))
            (term (FV/C C_2)))]
  [(FV/C (or/c C_1 C_2))
   ,(append (term (FV/C C_1))
            (term (FV/C C_2)))]
  [(FV/C (and/c C_1 C_2))
   ,(append (term (FV/C C_1))
         (term (FV/C C_2)))]
  [(FV/C (C_1 -> C_2))
   ,(append (term (FV/C C_1))
            (term (FV/C C_2)))]  
  [(FV/C C) ()])

(define-metafunction λc~
  set-minus : (any ...) any -> (any ...)
  [(set-minus (any_0 ...) any_1)
   ,(filter-not (λ (x) (equal? x (term any_1))) (term (any_0 ...)))])

(define-metafunction λc~
  closed? : C -> #t or #f
  [(closed? C) ,(empty? (term (FV/C C)))])
  
(test
 (test-equal (term (FV/C a)) (term (a)))
 (test-equal (term (FV/C any/c)) (term ()))
 (test-equal (term (closed? any/c)) #t)
 (test-equal (term (closed? a)) #f)
 (test-equal (term (closed? (rec/c a a))) #t)
 (test-equal (term (closed? (rec/c a b))) #f)
 (test-equal (term (closed? (rec/c a (rec/c b a)))) #t))

;; This is not a correct closed value, but just enough to make the
;; test generation work out.
(define-metafunction λc~
  FAKE-closed-value? : V -> #t or #f
  [(FAKE-closed-value? (-- C_0 C_1 ...)) 
   ,(andmap values (term ((closed? C_0) (closed? C_1) ...)))]
  [(FAKE-closed-value? (-- PV C ...))
   ,(andmap values (term ((closed? C) ...)))]
  [(FAKE-closed-value? V) #t])
  

(define-metafunction λc~
  valid? : C -> #t or #f
  [(valid? C) 
   ,(and (term (closed? C))
         (term (productive? C)))])

;; Ignores abstract values embeded in λs.
(define-metafunction λc~
  valid-value? : V -> #t or #f
  [(valid-value? (-- PV C ...))
   ,(andmap values (term ((valid? C) ...)))]
  [(valid-value? (-- C ...))
   ,(andmap values (term ((valid? C) ...)))])
  

(test
 
 (redex-check λc~ C* (redex-match λc~ C (term C*)))
 (redex-check λc~ WC!* (redex-match λc~ C (term WC!*)))
 (redex-check λc~ FVC!* (redex-match λc~ C (term FVC!*)))
 
 ;; Every valid contract is one of:
 ;; - WC?
 ;; - WC!
 ;; - FVC!
 (redex-check λc~ (side-condition C_1 (term (valid? C_1)))
              (or (redex-match λc~ WC? (term C_1))
                  (redex-match λc~ WC! (term C_1))
                  (redex-match λc~ FVC! (term C_1)))              
              #:attempts 10000)
 
 ;; No inhabited contract is in both of:
 ;; - WC?
 ;; - WC!
 ;; FIXME: need an inhabited? metafunction to make this work.
 #;
 (redex-check λc~ (side-condition C_1 (term (closed? C_1)))
              (not (and (redex-match λc~ WC? (term C_1))
                        (redex-match λc~ WC! (term C_1))))
              #:attempts 10000)
 
 ;; Completeness check for matching V with these patterns.
 ;; Used for case analysis in application rule.
 (redex-check λc~ (side-condition V_1 (and (term (FAKE-closed-value? V_1))
                                           (term (valid-value? V_1))))
              (or (redex-match λc~ W? (term V_1))
                  (redex-match λc~ WFV (term V_1)))                  
              #:attempts 10000))

(define (all-but-last ls)
  (drop-right ls 1))