#lang var rho eval
(module factorial racket 
  (define (fact-acc n acc)
    (if (zero? n) acc (fact-acc (sub1 n) (* n acc))))
  (define (fact.1 n) (fact-acc n 1))
  (define (fact n) 
    (cond [(zero? n) 1]
          [else (* n (fact (sub1 n)))]))
  
  (provide/contract 
   [fact.1 (exact-nonnegative-integer? . -> . exact-nonnegative-integer?)]
   [fact   (exact-nonnegative-integer? . -> . exact-nonnegative-integer?)]))
    

(module N racket (provide/contract [n exact-nonnegative-integer?]))
(require 'factorial 'N)
(fact.1 n)