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
  (L (λ (x ...) E) (λ x (x ...) E)) 
  (W (-- L C* ...))
  (bool #t #f)
  ;; Plain value
  (PV FV L)
  
  ;; A flat value is definitely not a procedure
  (FV nat bool string empty (cons V V))
  
  (V-or-x V x)
  
  ;; Values
  ((U V) WFV W)
  
  (WFV (-- FV C* ...))
  
  (SV L (f ^ f) o1) ; Syntactic values for pred.
  (E V PV x (f ^ ℓ) (@ E E ... ℓ) (if E E E) (@ o1 E ℓ) (@ o2 E E ℓ) (let x E E) (begin E E))
  
  (FLAT FLAT* x (and/c FLAT FLAT))
  (HOC HOC* (and/c HOC C)  (and/c C HOC) #;x)  ;; Not sure about x or no x.
  
  (FLAT* FC (pred SV ℓ) (cons/c FLAT FLAT) (or/c FLAT FLAT) (rec/c x FLAT))
  (HOC* (C ... -> C)
        (or/c FLAT HOC)
        (cons/c HOC C) (cons/c C HOC)
        (rec/c x HOC))
     
  (FC (pred nat? ℓ)
      (pred bool? ℓ)
      (pred string? ℓ)
      (pred empty? ℓ)
      (pred false? ℓ))
  
  (C* FLAT* HOC*)  
  (C FLAT HOC
     ;; Redundant [for random dist only]
     (pred nat? ℓ)
     (pred bool? ℓ)
     (pred string? ℓ)
     (pred empty? ℓ)
     (pred false? ℓ))
  
  (anyc (pred (λ (x) #t) ℓ))  ;; Could improve by any constant that is not #f.
  
  (x variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned)
  (ℓ f o † ★ Λ) ;; † is top-level, ★ is demonic generated, Λ is language generated
  (nat natural)
  (o o1 o2)
  (o1 o? nat->nat first rest)
  (nat->nat add1 sub1)
  ;; Built-in predicates
  (o? zero? proc? empty? cons? nat? string? bool? false?)
  (o2 nat*nat->nat nat*nat->bool cons)
  (nat*nat->nat + - * expt)
  (nat*nat->bool = < <= > >=)
  
  (𝓔 hole (@ V ... 𝓔 E ... ℓ) (if 𝓔 E E) (@ o V ... 𝓔 E ... ℓ) (let x 𝓔 E) (begin 𝓔 E)))

;; Figure 5, gray (cont).
(define-extended-language λc λc-user
  (B (blame ℓ ℓ V C V))
  (E .... (C <= ℓ ℓ V-or-x ℓ E) B)
  (𝓔 .... (C <= ℓ ℓ V ℓ 𝓔)))

;; Figure 5, gray (cont).
(define-extended-language λc~ λc
  (AE (-- C* C* ...))      ;; Abstract expressions
  (AV (-- C*-top C*-top ...))  ;; Abstract values
  (CV (-- PV C*-top ...))      ;; Concrete values
  (C-ext C λ)
      
  (V-or-AE V AE)
  (E .... AE (C <= ℓ ℓ AE ℓ E))
  (𝓔 .... (C <= ℓ ℓ AE ℓ 𝓔))
  (B ....
     (blame ℓ ℓ AE C V) 
     (blame ℓ ℓ V λ V)) ;; broke the contract with the language
  
  (WFV .... (-- C*-top ... FVC!*-top C*-top ...))
  
  ;; Representations of abstract values
  ;; no or/c or rec/c at top-level
  (C*-top (pred SV ℓ)
          (C ... -> C)
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

  (V-or-B V B)
  
  ;; Definite procedure contract
  (WC! WC!* (and/c C WC!) (and/c WC! C))
  (WC!* WC!*-top (rec/c x WC!))
  (WC!*-top (C ... -> C) (pred proc? ℓ))
  
  ;; Definite procedure  
  (W .... (-- C*-top ... WC!*-top C*-top ...))
  
    
  ;; Note: uninhabited contracts may be both definitely flat and procedures.
  
  ;; Maybe procedure contract
  (WC? WC?* (and/c WC? WC?))  
  (WC?* WC?*-top
        (or/c WC? C)
        (or/c C WC?)       
        (or/c FVC! WC!)
        (or/c WC! FVC!)       
        (rec/c x WC?))  
  (WC?*-top (pred (side-condition SV_1 (not (equal? (term SV_1) 'proc?))) ℓ))

  ;; Maybe procedure
  (W? W (-- C*-top ... WC?*-top C*-top ...))
  
  ;; Raw, unannotated language
  (RP (RM ... RE))
  (RM (module f RC RPV) (module f RC ☁))
  (RL (λ (x ...) RE) (λ x (x ...) RE))
  (RPV FV RL)  
  (RSV RL f o1) ; Syntactic values for pred.
  (RE RPV x f (RE RE ...) (if RE RE RE) (o1 RE) (o2 RE RE) (let x RE RE) (begin RE RE))
  
  
  (RCFLAT o? anything (pred RSV) (cons/c RCFLAT RCFLAT) (or/c RCFLAT RCFLAT) (and/c RCFLAT RCFLAT)
          (rec/c x RCFLAT) x)
  (RCHOC (RC ... -> RC)
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
  [(productive? (C_1 ... -> C_2) x_0 ...)
   ,(and (andmap (λ (c) (term (productive? ,c))) (term (C_1 ...)))
         (term (productive? C_2)))]
  [(productive? (or/c C_1 C_2) x_0 ...)
   ,(and (term (productive? C_1 x_0 ...))
         (term (productive? C_2 x_0 ...)))]
  [(productive? (and/c C_1 C_2) x_0 ...)
   ,(and (term (productive? C_1 x_0 ...))
         (term (productive? C_2 x_0 ...)))]
  [(productive? C x ...) #t])

(define-syntax-rule 
  (/c name p)  
  (define-metafunction λc~
    name : -> C
    [(name) (pred p Λ)]))

(/c any/c (λ (x) #t))
(/c nat/c nat?)
(/c string/c string?)
(/c empty/c empty?)
(/c bool/c bool?)
(/c false/c false?)

(test
 (test-equal (term (productive? (pred (λ (x) #t) f))) #t)
 (test-equal (term (productive? (rec/c x x))) #f)
 (test-equal (term (productive? (or/c (any/c) (rec/c x x)))) #f)
 (test-equal (term (productive? (rec/c x (or/c (empty/c) (cons/c (any/c) x))))) #t)
 (test-equal (term (productive? ((any/c) -> (any/c)))) #t)
 (test-equal (term (productive? (or/c (rec/c a a) ((any/c) -> (any/c))))) #f))

(test
 (test-equal (redex-match λc~ AV (term (-- (any/c) (and/c (nat/c) (nat/c)))))
             #f))

(define abstract-value? (redex-match λc~ (-- C* ...)))
(define (final-state? x)
  (or (redex-match λc~ V x)
      (redex-match λc~ B x)
      (redex-match λc~ (-- C_0 ...  C_1 ...))))

(define-metafunction λc~
  set-minus : (any ...) (any ...) -> (any ...)
  [(set-minus any_0 any_1)
   ,(set->list (set-subtract  (apply set (term any_0))
                              (apply set (term any_1))))])

(define-metafunction λc~
  FV/C : C -> (x ...)
  [(FV/C x) (x)]
  [(FV/C (rec/c x C))
   (set-minus (FV/C C) (x))]
  [(FV/C (cons/c C_1 C_2))
   ,(append (term (FV/C C_1))
            (term (FV/C C_2)))]
  [(FV/C (or/c C_1 C_2))
   ,(append (term (FV/C C_1))
            (term (FV/C C_2)))]
  [(FV/C (and/c C_1 C_2))
   ,(append (term (FV/C C_1))
         (term (FV/C C_2)))]
  [(FV/C (C_1 ... -> C_2))
   ,(append (apply append (map (λ (c) (term (FV/C ,c))) (term (C_1 ...))))
            (term (FV/C C_2)))]  
  [(FV/C C) ()])

(define-metafunction λc~
  closed? : C -> #t or #f
  [(closed? C) ,(empty? (term (FV/C C)))])
  
(test
 (test-equal (term (FV/C a)) (term (a)))
 (test-equal (term (FV/C (any/c))) (term ()))
 (test-equal (term (closed? (any/c))) #t)
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

(define-metafunction λc~
  fv : E -> (x ...)
  [(fv x) (x)]
  [(fv (f ^ ℓ)) ()]
  [(fv (λ (x ...) E)) (set-minus (fv E) (x ...))]
  [(fv (let x E_1 E_2)) 
   (x_1 ... x_2 ...)
   (where (x_2 ...) (set-minus (fv E_2) (x)))
   (where (x_1 ...) (fv E_1))]
  [(fv (λ x_0 (x ...) E)) (set-minus (fv E) (x_0 x ...))]
  [(fv PV) ()]
  [(fv (-- PV C ...)) (fv PV)]
  [(fv (-- C ...)) ()]
  [(fv (if E ...)) (fv/list (E ...))]
  [(fv (begin E ...)) (fv/list (E ...))]
  [(fv (@ E ... ℓ)) (fv/list (E ...))]
  [(fv (@ o E ... ℓ)) (fv/list (E ...))]
  [(fv (C <= ℓ_1 ℓ_2 any_1 ℓ_3 E)) (fv E)]
  [(fv (blame ℓ_1 ℓ_2 V-or-AE any_C V)) (fv/list (V-or-AE V))])

(define-metafunction λc~
  fv/list : (E ...) -> (x ...)
  [(fv/list (E ...)) (x ... ...)
   (where ((x ...) ...) ((fv E) ...))])
  

(test
 
 (test-equal
  (redex-match λc~ HOC (term (cons/c
                              (nat/c)
                              (cons/c
                               (rec/c
                                X
                                (or/c
                                 (nat/c)
                                 (cons/c
                                  (nat/c)
                                  (cons/c X X))))
                               (rec/c
                                X
                                (or/c
                                 (nat/c)
                                 (cons/c
                                  (nat/c)
                                  (cons/c X X))))))))
  #f)
 
 (redex-check λc~ C* (redex-match λc~ C (term C*)))
 (redex-check λc~ WC!* (redex-match λc~ C (term WC!*)))
 (redex-check λc~ FVC!* (redex-match λc~ C (term FVC!*)))
 
 ;; Every contract is FLAT xor HOC.
 (redex-check λc~ (side-condition C_1 (term (valid? C_1)))
              (or (and (redex-match λc~ FLAT (term C_1))
                       (not (redex-match λc~ HOC (term C_1))))
                  (and (redex-match λc~ HOC (term C_1))
                       (not (redex-match λc~ FLAT (term C_1)))))
              #:attempts 10000)
 
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