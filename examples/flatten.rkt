#lang var fast

(define-contract list/c
  (rec/c X (or/c empty? (cons/c exact-nonnegative-integer? X))))

(module F racket  
  (define append 
    (λ (l1 l2)
      (cond [(empty? l1) l2]
            [else (cons (first l1) (append (rest l1) l2))])))
  (define (flatten l)
    (cond [(empty? l) empty]
          [(cons? l) (append (flatten (first l)) (flatten (rest l)))]
          [else (cons l empty)]))
  (provide/contract [flatten (anything . -> . list/c)]))
(module L racket
  (provide/contract [l anything]))
(require 'F 'L)
(flatten l)
