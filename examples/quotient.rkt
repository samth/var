#lang var rho
(module positive racket
  (provide/contract [n (and/c exact-nonnegative-integer?
                              (not/c zero?))]))
(require 'positive)
(quotient 3 n)