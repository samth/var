#lang var rho

(define-contract form/c (rec/c X (or/c boolean? (-> boolean? X))))

(module T racket
  (define (taut b)
    (cond
      [(boolean? b) b]
      [else (if (taut (b #t))
                (taut (b #f))
                #f)]))
  (provide/contract [taut (-> form/c boolean?)]))
(module F racket
  (provide/contract [f form/c]))
(require 'T 'F)
(taut f)

