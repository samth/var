#lang var trace
(module m racket 
  (struct s (x y z))
  (provide/contract [s any?]))

(require m)
(s 7)