#lang var ;trace
(module factorial racket 
  (define (fact m) 
    ((λ g (n)
       (if (zero? n)
           1
           (* n (g (sub1 n)))))
     m))
  
  (provide/contract [fact (-> exact-nonnegative-integer? exact-nonnegative-integer?)]))
    
(require factorial)
(fact 5)