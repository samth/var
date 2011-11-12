#lang var rho trace
(module m racket
  (define f (λ (n . r) r))
  #;(provide/contract [f ((exact-nonnegative-integer?) #:rest (listof any/c) . ->* . (listof any/c))])
  (provide/contract [f any/c]))
  

(require 'm)
(f 5 1 2 3 4 5 6 7 8 9 10)