#lang var rho
(module m racket
  (struct posn (x y))
  (define (p) (posn 1 2))
  (provide/contract [p (-> (struct/c posn exact-nonnegative-integer? exact-nonnegative-integer?))]))

(require 'm)
(p)
