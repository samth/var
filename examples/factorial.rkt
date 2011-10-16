#lang var ;trace
(module factorial racket 
  (define (fact n) 
    (if (zero? n)
        1
        (* n (fact (sub1 n)))))
  
  (provide/contract 
   [fact (-> exact-nonnegative-integer? exact-nonnegative-integer?)]))
    
(require 'factorial)
(fact 5)