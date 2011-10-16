#lang var ;trace
(define/contract fact
  (-> exact-nonnegative-integer? exact-nonnegative-integer?)
  (λ (n)
    (if (zero? n)
        1
        (* n (fact (sub1 n))))))
  
(require 'fact)
(fact 5)