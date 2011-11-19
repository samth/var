#lang var rho
;;--------------------------------------------------------------------
;; Occurrence typing-style reasoning, infeasible blame
(module opaque racket
  (provide/contract [a any/c]))

(module m racket
  (define (f x)
    (if (cons? x) (car x) x))
  (provide/contract [f (any/c . -> . any/c)]))

(require 'm 'opaque)
(f a)