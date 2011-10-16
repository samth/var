#lang var trace
;; This program runs forever.

#;#;
(define/contract mul (nat/c -> (nat/c -> nat/c)) ☁)
(define/contract 1- (nat/c -> nat/c) ☁)


(module fact racket
  (require)
  (define (fact-acc x acc)
    (if (= x 0)
        acc
        (fact-acc (sub1 x) (* acc x))))
  (define (fact in) (fact-acc in 1))
  (provide/contract [fact (nat? -> nat?)]))

(define/contract input nat? ☁)
(require (only-in fact fact) (only-in input input))

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