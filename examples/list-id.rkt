#lang var rho
(module o racket
  (provide/contract [l (listof any/c)]))

(module f racket
  (define (ls-id x)
    (if (empty? x) 
        x
        (cons (car x)
              (ls-id (cdr x)))))
  (provide/contract 
   [ls-id ((listof any/c) . -> . (listof any/c))]))

(require 'o 'f)
(ls-id l)