#lang var #;trace
(module e/o racket 
  (define even? (λ (n) (if (zero? n) #t (odd? (sub1 n)))))
  (define odd?
    (λ (n) (if (zero? n) #f (even? (sub1 n)))))
  (provide/contract [even? (-> exact-nonnegative-integer? boolean?)]
                    [odd? (-> exact-nonnegative-integer? boolean?)]))

(module dbl racket
  (require (only-in 'e/o even?))
  (define dbl (λ (f) (λ (x) (f (f x)))))
  (provide/contract [dbl (-> (-> even? even?) (-> even? even?))]))

(module fun racket
  (require (only-in 'e/o even?))
  ;...
  (provide/contract [fun (-> even? even?)]))

(require 'dbl 'fun)
((dbl fun) 4)
