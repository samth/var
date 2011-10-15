
#lang s-exp "verified.rkt" trace

(module dbl racket
  (require)
  (define (dbl f) (λ (x) (f (f x))))
  (provide/contract [dbl ((zero? -> zero?) -> (zero? -> zero?))]))

(module f racket 
  (require)
  (define (f x) 7)
  (provide/contract [f (zero? -> nat?)]))

(require (only-in f f) (only-in dbl dbl))
((dbl f) 0)
