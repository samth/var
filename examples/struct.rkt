#lang var trace
(module m racket
  (require) 
  (struct s (x y z))
  (provide/contract [make-s any]))

(require (only-in m make-s))
(make-s 7)