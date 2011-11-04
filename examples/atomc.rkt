#lang var rho trace
(module a racket
  (define (f x) x)
  (provide/contract [f ('zoo . -> . 'zoo)]))

(module b racket
  (provide/contract [z 'zoo]))

(require 'a 'b)
(f z)
