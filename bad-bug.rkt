#lang s-exp "verified.rkt" trace

(module dbl ((zero? -> zero?) -> (zero? -> zero?))
 (λ (f) (λ (x) (f (f x)))))

(module f (zero? -> nat?)
 (λ (x) 7))

((dbl f) 0)
