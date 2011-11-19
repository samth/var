#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide m)
(test-suite test step-m)

(define (m Ms)
  (reduction-relation
   λcρ #:domain (D σ)
   (--> ((X_1 ^ X X) σ)
        (V σ)
        (where V (lookup-modref/val X_1 X X ,Ms))
        m-self)
   (--> ((X_1 ^ LAB X) σ)
        ((CON (env) <= X LAB V X_1 V) σ)
        (where CON (lookup-modref/con X_1 LAB X ,Ms))
        (where V (lookup-modref/val X_1 LAB X ,Ms))
        (side-condition (not (eq? (term X) (term LAB))))
        m-other)))
    
(test 
 (define Ms 
   (term [(module m racket 
            (require) 
            (struct posn (x y))
            (define f 1)
            (define c (cons 2 3))
            (provide/contract 
             [f (pred string? m)]
             [posn? ((pred (λ (x) #t) m) -> (pred boolean? m))]
             [posn ((pred exact-nonnegative-integer? m)
                    (pred exact-nonnegative-integer? m)
                    -> (pred (posn? ^ m m) m))]
             [posn-x ((pred (posn? ^ m m) m) -> (pred exact-nonnegative-integer? m))]
             [posn-y ((pred (posn? ^ m m) m) -> (pred exact-nonnegative-integer? m))]
             [c (pred cons? m)]))]))
 (test/σ--> (m Ms)
            (term (f ^ m m))
            (term (-- (↓ 1 (env)))))
 (test/σ--> (m Ms)
            (term (f ^ † m))
            (term ((pred string? m) (env) <= m † (-- (↓ 1 (env))) f (-- (↓ 1 (env))))))
 (test/σ--> (m Ms)
            (term (posn ^ m m))
            (term (-- (↓ (s-cons posn 2) (env)))))
 (test/σ--> (m Ms)
            (term (posn? ^ m m))
            (term (-- (↓ (s-pred posn) (env)))))
 (test/σ--> (m Ms)
            (term (posn-x ^ m m))
            (term (-- (↓ (s-ref posn 0) (env)))))
 (test/σ--> (m Ms)
            (term (posn-y ^ m m))
            (term (-- (↓ (s-ref posn 1) (env)))))
 (test/σ--> (m Ms)
            (term (c ^ m m))
            (term (-- (cons (-- (↓ 2 (env)))
                            (-- (↓ 3 (env))))))))



