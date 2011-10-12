#lang s-exp "../verified.rkt" #;trace
(module dbl ((even? -> even?) -> 
             (even? -> even?))
  (λ (f) (λ (x) (f (f x)))))
(module even? (nat? -> bool?) 
  (λ (n) (if (zero? n) #t (odd? (sub1 n)))))
(module odd? (nat? -> bool?) 
  (λ (n) (if (zero? n) #f (even? (sub1 n)))))
(module fun (even? -> even?) ●)

((dbl fun) 4)
