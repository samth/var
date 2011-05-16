#lang racket
(require redex)
(provide (all-defined-out))

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
  
  (V WFV W)
  (WFV (-- FV C ...))
  
  (SV L (f ^ f)) ; Syntactic values for pred.  [Different than paper] --STH-- FIXME:  should be ℓ
  (E V PV x (f ^ ℓ) (@ E E ℓ) (if E E E) (@ o1 E ℓ) (@ o2 E E ℓ) (let x E E) (begin E E))
  (FC nat/c bool/c string/c empty/c)
  (C any/c none/c (C -> C) (pred SV) (cons/c C C) FC)
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
  (W .... ((C --> C) <= ℓ ℓ V ℓ W))  
  (B (blame ℓ ℓ V C V))
  (E .... (C <= ℓ ℓ V ℓ E) B)
  (C .... (C --> C))
  ;(f .... Λ)
  (𝓔 .... (C <= ℓ ℓ V ℓ 𝓔)))

;; Figure 5, gray (cont).
(define-extended-language λc~ λc
  (AV (-- C C ...))
  (C-ext C λ)
      
  (WFV .... anat astring abool acons aempty)    
  (V .... AV)             ;; (-- X) is overline X.
  (B .... (blame ℓ ℓ V λ V)) ;; broke the contract with the language
  (M .... (module f C ☁))
  
  ;; Definite procedure  
  (W .... (-- C ... (C -> C) C ...))
    
  ;; Maybe procedure
  (W? W (-- any/c C ...) (-- (pred SV) C ...))    
  
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
  (RC any/c none/c (RC -> RC) (pred RSV) (cons/c RC RC) FC))

(define abstract-value? (redex-match λc~ (-- C ...)))
(define (final-state? x)
  (or (redex-match λc~ V x)
      (redex-match λc~ B x)
      (redex-match λc~ (-- C_0 ... none/c C_1 ...))))

(redex-check λc~ V  
             (or (redex-match λc~ W? (term V))
                 (redex-match λc~ WFV (term V))
                 (redex-match λc~ (-- any_0 ... (C_0 --> C_1) any_1 ...) (term V))
                 (redex-match λc~ (-- C_0 ... none/c C_1 ...) (term V)))
             #:attempts 1000)             

(define (all-but-last ls)
  (drop-right ls 1))