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
  (W (-- L C ...))
  (bool #t #f)
  (PV FV L)
  (FV nat bool string empty (cons V V))
  
  (V-or-x V x)
  
  (V WFV W)
  (WFV (-- FV C ...))
  
  (SV L (f ^ f)) ; Syntactic values for pred.  [Different than paper]
  (E V PV x (f ^ ℓ) (@ E E ℓ) (if E E E) (@ o1 E ℓ) (@ o2 E E ℓ) (let x E E) (begin E E))
  
  (FLAT FC any/c none/c (pred SV ℓ) (cons/c FLAT FLAT) (or/c FLAT FLAT) (and/c FLAT FLAT))
  (HOC (C -> C)
       (or/c FLAT HOC)
       (cons/c HOC C) (cons/c C HOC)
       (and/c HOC C)  (and/c C HOC))
  
  (FLAT* FC any/c none/c (pred SV ℓ) (cons/c FLAT FLAT) (or/c FLAT FLAT))
  (HOC* (C -> C)
        (or/c FLAT HOC)
        (cons/c HOC C) (cons/c C HOC))
    
  (FC nat/c bool/c string/c empty/c)
  (C* FLAT* HOC*)  
  (C FLAT HOC)
  
  (x variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned)
  (ℓ f o † ★ Λ) ;; † is top-level, ★ is demonic generated, Λ is language generated
  (nat natural)
  (o o1 o2)
  (o1 add1 sub1 zero? proc? empty? cons? first rest)
  (o2 + - * expt = < <= > >= cons)
  (𝓔 hole (@ 𝓔 E ℓ) (@ V 𝓔 ℓ) (if 𝓔 E E) (@ o V ... 𝓔 E ... ℓ) (let x 𝓔 E) (begin 𝓔 E)))
  
;; Figure 5, gray (cont).
(define-extended-language λc λc-user
  (B (blame ℓ ℓ V C V))
  (E .... (C <= ℓ ℓ V-or-x ℓ E) B)
  (𝓔 .... (C <= ℓ ℓ V ℓ 𝓔)))

;; Figure 5, gray (cont).
(define-extended-language λc~ λc
  (AV (-- C* C* ...))
  (C-ext C λ)
      
  (WFV .... anat astring abool acons aempty)
  (V .... AV)             ;; (-- X) is overline X.
  (B .... (blame ℓ ℓ V λ V)) ;; broke the contract with the language
  (M .... (module f C ☁))
  
  ;; Definite procedure  
  (W .... (-- C ... (C -> C) C ...))
    
  ;; Maybe procedure contract
  (WC? any/c
       (pred SV ℓ)
       (or/c WC? C)
       (or/c C WC?)
       (or/c C (C -> C))
       (or/c C (and/c (C -> C) C))
       (or/c C (and/c C (C -> C)))
       (and/c WC? WC?))
  
  ;; Maybe procedure
  (W? W (-- WC? C ...))
  
  ;; Contracts that always fail
  (NC none/c
      (or/c NC NC)
      (and/c NC C)
      (and/c C NC))
  
  
  ;; Flat, wrapped concrete and abstract values
  (anat (-- nat C ...) (-- C ... nat/c C ...))
  (astring (-- string C ...) (-- C ... string/c C ...))
  (abool (-- bool C ...) (-- C ... bool/c C ...))
  (aempty (-- empty C ...) (-- C ... empty/c C ...))
  (acons (-- (cons V V) C ...) (-- C ... (cons/c C C) C ...))
  
  ;; Raw, unannotated language
  (RP (RM ... RE))
  (RM (module f RC RPV) (module f RC ☁))
  (RL (λ x RE) (λ x x RE))
  (RPV FV RL)  
  (RSV RL f) ; Syntactic values for pred.  [Different than paper]
  (RE RPV x f (RE RE) (if RE RE RE) (o1 RE) (o2 RE RE) (let x RE RE) (begin RE RE))
  
  
  (RCFLAT FC any/c none/c (pred RSV) (cons/c RCFLAT RCFLAT) (or/c RCFLAT RCFLAT) (and/c RCFLAT RCFLAT))
  (RCHOC (RC -> RC)
         (or/c RCFLAT RCHOC)
         (cons/c RCHOC RC) (cons/c RC RCHOC)
         (and/c RCHOC RC)  (and/c RC RCHOC))
  
  (RC RCFLAT RCHOC))
  
(test
 (test-equal (redex-match λc~ AV (term (-- any/c (and/c nat/c nat/c))))
             #f))

(define abstract-value? (redex-match λc~ (-- C ...)))
(define (final-state? x)
  (or (redex-match λc~ V x)
      (redex-match λc~ B x)
      (redex-match λc~ (-- C_0 ... none/c C_1 ...))))

(test
 ;; Completeness check for matching V with these patterns.
 (redex-check λc~ V  
              (or (redex-match λc~ W? (term V))
                  (redex-match λc~ WFV (term V))
                  (redex-match λc~ (-- C_0 ... NC C_1 ...) (term V)))
              #:attempts 10000))

(define (all-but-last ls)
  (drop-right ls 1))