#lang racket
(require redex)

;; Symbolic Core Racket
(define-language SCR
  ; program
  [(P Q) (M ... E)]
  ; module
  [(M N) (module f C V)]
  [E (f l)
     X
     A
     ((E E) l)
     (if E E E)
     (O E ...)
     (μ X E)
     (mon f f f C E)]
  ; prevalue
  [U n
     tt ff
     (λ X E)
     •
     (V V)
     empty]
  ; value
  [V (U Cs)]
  ; contract
  [(C D) X
         (C ↦ (λ X C))
         (flat E)
         (C C)
         (C ∨ C)
         (C ∧ C)
         (μ X C)]
  [(Cs Ds) (C ...)]
  ; primitive ops
  [O add1 car cdr cons + = o?]
  [o? nat? bool? empty? cons? proc? false?]
  ; answer
  [A V
     (blame l l)]
  [(X Y Z f g h l) variable-not-otherwise-mentioned])