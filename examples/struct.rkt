#lang var rho eval
(module m racket 
  (struct s (x y z))
  (provide/contract [s any/c]))

(require 'm)
(s 7 8) ; blame † on Λ, expects 3 arguments