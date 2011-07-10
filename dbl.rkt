#lang s-exp "verified.rkt" cesk

(module dbl (((pred even?) -> (pred even?)) -> ((pred even?) -> (pred even?)))
  (λ (f) (λ (x) (f (f x)))))

(module even? (nat? -> bool?) (λ (n) (if (zero? n) #t (odd? (sub1 n)))))
(module odd? (nat? -> bool?) (λ (n) (if (zero? n) #f (even? (sub1 n)))))

(module fun #;anything ((pred even?) -> (pred even?)) • #;(λ (z) 7))

((dbl fun) 4)

