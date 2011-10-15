#lang s-exp "verified.rkt"
(define/contract even? (nat? -> bool?) 
  (λ (n) (if (zero? n) #t (odd? (sub1 n)))))
(define/contract odd? (nat? -> bool?) 
  (λ (n) (if (zero? n) #f (even? (sub1 n)))))

(define/contract dbl ((even? -> even?) -> (even? -> even?))
  (λ (f) (λ (x) (f (f x)))))

((dbl (λ (x) 7)) 8)