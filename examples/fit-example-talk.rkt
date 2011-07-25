#lang s-exp "../verified.rkt" trace
;; This program runs forever.

#;#;
(module mul (nat/c -> (nat/c -> nat/c)) ☁)
(module 1- (nat/c -> nat/c) ☁)


(module fact (nat/c -> nat/c)
  (λ in
    (((λ f x
      (λ acc
        (if (= x 0)
            acc
            ((f (sub1 x)) (* acc x)))))
     in) 1)))

(module input nat/c ☁)

(fact input)

#|

;(module mul (nat/c -> (nat/c -> nat/c)) ☁)
;(module 1- (nat/c -> nat/c) ☁)

(module fact (nat/c -> nat/c)
  (λ x
    (if (= x 0)
        1
        (* x (fact (sub1 x))))))

(module input nat/c ☁)

(fact input)
|#