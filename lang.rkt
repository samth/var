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
  (FV nat bool string)
  
  (V WFV W)
  (WFV (-- FV C ...))
  
  (SV L (f ^ f)) ; Syntactic values for pred.  [Different than paper]
  (E V PV x (f ^ f) (@ E E f) (if E E E) (@ o1 E f) (@ o2 E E f) (let x E E) (begin E E))
  (FC nat/c bool/c string/c)
  (C any/c none/c (C -> C) (pred SV) FC)
  (x variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned o † ★) ;; † is top-level
  (nat natural)
  (o o1 o2)
  (o1 add1 sub1 zero? proc?)
  (o2 + - * expt = < <= > >=)
  (𝓔 hole (@ 𝓔 E f) (@ V 𝓔 f) (if 𝓔 E E) (@ o V ... 𝓔 E ... f) (let x 𝓔 E) (begin 𝓔 E)))
  
;; Figure 5, gray (cont).
(define-extended-language λc λc-user
  (W .... ((C --> C) <= f f V f W))  
  (B (blame f f V C V))
  (E .... (C <= f f V f E) B)
  (C .... (C --> C))
  (f .... Λ)
  (𝓔 .... (C <= f f V f 𝓔)))

;; Figure 5, gray (cont).
(define-extended-language λc~ λc
  (AV (-- C C ...))
  
  (C-ext C λ)
      
  (WFV .... anat astring abool)
  (V .... AV)             ;; (-- X) is overline X.
  (B .... (blame f f V λ V)) ;; broke the contract with the language
  (M .... (module f C ☁))
  
  ;; Definite procedure  
  (W .... (-- C ... (C -> C) C ...))
    
  ;; Maybe procedure
  (W? W (-- any/c C ...) (-- (pred SV) C ...))    
  
  (anat (-- nat C ...) (-- C ... nat/c C ...))
  (astring (-- string C ...) (-- C ... string/c C ...))
  (abool (-- bool C ...) (-- C ... bool/c C ...))
  
  ;; Raw, unannotated language
  (RP (RM ... RE))
  (RM (module f RC RPV) (module f RC ☁))
  (RL (λ x RE) (λ x x RE))
  (RPV FV RL)  
  (RSV RL f) ; Syntactic values for pred.  [Different than paper]
  (RE RPV x f (RE RE) (if RE RE RE) (o1 RE) (o2 RE RE) (let x RE RE) (begin RE RE))
  (RC any/c none/c (RC -> RC) (pred RSV) FC))

(define anat? (redex-match λc~ anat))
(define astring? (redex-match λc~ astring))
(define abool? (redex-match λc~ abool))
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