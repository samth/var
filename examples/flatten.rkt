#lang var rho
(module F racket  
  (define append 
    (λ (l1 l2)
      (cond [(empty? l1) l2]
            [else (cons (car l1) (append (cdr l1) l2))])))
  (define (flatten l)
    (cond [(empty? l) empty]
          [(cons? l) (append (flatten (car l)) (flatten (cdr l)))]
          [else (cons l empty)]))
  (provide/contract [flatten (any/c . -> . (listof exact-nonnegative-integer?))]))
(module L racket
  (provide/contract [l any/c]))
(require 'F 'L)
(flatten l)
