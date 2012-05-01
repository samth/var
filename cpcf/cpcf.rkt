#lang racket
(require redex)

;; PCF with Contracts
(define-language CPCF
  ; terms
  [(M N L) A
           X
           (M M)
           (μ (X T) M)
           (if M M M)
           (o1 M)
           (o2 M M)
           ; h,f,g: original, positive, negative
           (mon h f g C M)]
  ; types
  [T B
     (T → T)
     (con T)]
  [B n b]
  [(m n) integer]
  [b tt ff]
  ; primitive ops
  [o o1 o2]
  [o1 zero? even? odd? true? false?]
  [o2 + - ∨ ∧]
  ; contracts
  [(C D) (flat M)
         (C ↦ C)
         (C ↦ (λ (X T) C))]
  ; answers
  [A V
     (blame f g)] ; f breaks its contract with g
  ; values
  [V (λ (X T) M)
     n
     b]
  ; evaluation contexts
  [E hole
     (E M)
     (V E)
     (o V ... E M ...)
     (if E M M)
     (mon h f g C E)])
           