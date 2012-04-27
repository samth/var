#lang var step

(module m racket
  (define (f x) (if (= x 0) 1 x))
  (provide/contract [f (->d ([x any/c]) [r (λ (v) (= v x))])]))

(require 'm)

(f 0)
