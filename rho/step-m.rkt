#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide m)
(test-suite test step-m)

(define (m Ms)
  (reduction-relation
   λcρ #:domain D
   (--> (X_1 ^ X X)
        (-- (clos VAL ()))
        (where VAL (lookup-modref/val X X_1 ,Ms))
        m-self)
   (--> (X_1 ^ LAB X)
        (CON () <= X LAB V X_1 V)
        (where CON (lookup-modref/con X X_1 ,Ms))
        (where VAL (lookup-modref/val X X_1 ,Ms))
        (where V (-- (clos VAL ())))
        (side-condition (not (eq? (term X) (term LAB))))
        m-other)))

(test 
 (define Ms 
   (term [(module m racket 
            (require) 
            (define f 1)
            (provide/contract [f (pred string? m)]))]))
 (test--> (m Ms)
          (term (f ^ m m))
          (term (-- (clos 1 ()))))
 (test--> (m Ms)
          (term (f ^ † m))
          (term ((pred string? m) () <= m † (-- (clos 1 ())) f (-- (clos 1 ()))))))
