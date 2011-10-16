#lang var #;trace
(module e/o racket 
  (require)
  (define even? (λ (n) (if (zero? n) #t (odd? (sub1 n)))))
  (define odd?
    (λ (n) (if (zero? n) #f (even? (sub1 n)))))
  (provide/contract [even? (-> nat? bool?)]
                    [odd? (-> nat? bool?)]))

(module dbl racket
  (require (only-in e/o even?))
  (define dbl (λ (f) (λ (x) (f (f x)))))
  (provide/contract [dbl (-> (-> even? even?) (-> even? even?))]))

(module fun racket
  (require (only-in e/o even?))
  (provide/contract [fun (-> even? even?)]))
(require (only-in dbl dbl) (only-in fun fun))
((dbl fun) 4)
