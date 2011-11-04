#lang var rho
(module s racket
  (provide/contract [s (list/c (symbols 'a 'b 'c)
                               (one-of/c 3 'd))]))

(require 's)
(symbol? (car s))

