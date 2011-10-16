#lang var
(module e/o racket
  (define even? (λ (n) (if (zero? n) #t (odd? (sub1 n)))))
  (define odd?
    (λ (n) (if (zero? n) #f (even? (sub1 n)))))
  (provide/contract [even? (-> exact-nonnegative-integer? bool?)]
                    [odd? (-> exact-nonnegative-integer? bool?)]))

(module dbl racket
  (require e/o)
  (define dbl (λ (f) (λ (x) (f (f x)))))
  (provide/contract [dbl (-> (-> even? even?) (-> even? even?))]))

(require dbl)

((dbl (λ (x) 7)) 8)