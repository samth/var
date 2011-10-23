#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide m~)
(test-suite test step-m-abs)

(define (m~ Ms)
  (reduction-relation
   λcρ #:domain D
   (--> (X_1 ^ LAB X)
        (CON () <= X LAB (-- (CON ())) X_1 
             (remember-contract (-- ((pred (λ (x) #t) Λ) ())) (CON ())))
        (where • (lookup-modref/val X X_1 ,Ms))
        (where CON (lookup-modref/con X X_1 ,Ms))
        (side-condition (not (eq? (term X) (term LAB))))
        m-opaque)))

(test
 (define Ms 
   (term [(module m racket 
            (require) 
            (define f •)
            (provide/contract [f (pred string? m)]))]))
 
 (test--> (m~ Ms)
          (term (f ^ † m))
          (term ((pred string? m) 
                 () <= m † (-- ((pred string? m) ())) f 
                 (-- ((pred string? m) ()))))))