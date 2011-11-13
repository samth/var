#lang var rho
(module dbl racket  
  (define (dbl f) (λ (x) (f (f x))))
  (provide/contract [dbl (-> (-> zero? zero?) (-> zero? zero?))]))

(module f racket 
  ;(define (f x) 7)
  (provide/contract [f (-> zero? exact-nonnegative-integer?)]))

(require 'f 'dbl)
((dbl f) 0)
