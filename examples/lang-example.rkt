#lang var

(define-contract any/c any?)

(define/contract f (any/c -> (any/c -> any/c)) ☁)
(define/contract g ((pred (λ (x) x)) -> nat?) ☁ )
(module h racket
  (require (only-in f f) (only-in g g))
  (define h (λ (z) ((f g) #f)))
  (provide/contract [h any/c]))
(require (only-in h h))
(h 0)
         
