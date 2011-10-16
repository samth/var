#lang var ;trace
(module factorial racket 
  (define (fact n) 
    (cond [(zero? n) 1]
          [else (* n (fact (sub1 n)))]))
  
  (provide/contract 
   [fact (exact-nonnegative-integer? . -> . exact-nonnegative-integer?)]))
    
(require 'factorial)
(fact 5)