#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide m~)
(test-suite test step-m-abs)

(define (m~ Ms)
  (reduction-relation
   λcρ #:domain (D σ)
   (--> ((X_1 ^ LAB X) σ)
        ((CON (env) <= X LAB V_1 X_1 V_1) σ)
        (where • (lookup-modref/val X_1 LAB X ,Ms))
        (where CON (lookup-modref/con X_1 LAB X ,Ms))
        (where (any_1 ... V_1 any_2 ...)
               (remember-contract/any (-- ((pred (λ (x) #t) Λ) (env))) (CON (env))))
        (side-condition (not (eq? (term X) (term LAB))))
        m-opaque)))

(test
 (define Ms 
   (term [(module m racket 
            (require) 
            (define f •)
            (provide/contract [f (pred string? m)]))]))
 
 (test/σ--> (m~ Ms)
            (term (f ^ † m))
            (term ((pred string? m) 
                   (env) <= m † (-- ((pred string? m) (env))) f 
                   (-- ((pred string? m) (env)))))))
