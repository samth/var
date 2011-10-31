#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide m)
(test-suite test step-m)

(define (m Ms)
  (reduction-relation
   λcρ #:domain D
   (--> (X_1 ^ X X)
        (push-close VAL)
        (where VAL (lookup-modref/val X X_1 ,Ms))
        m-self)
   (--> (X_1 ^ LAB X)
        (CON (env) <= X LAB (push-close VAL) X_1 (push-close VAL))
        (where CON (lookup-modref/con X X_1 ,Ms))
        (where VAL (lookup-modref/val X X_1 ,Ms))        
        (side-condition (not (eq? (term X) (term LAB))))
        m-other)))

(define-metafunction λcρ
  push-close : VAL -> D
  [(push-close (cons VAL_1 VAL_2))
   (-- (cons (push-close VAL_1)
             (push-close VAL_2)))]
  [(push-close VAL)
   (-- (clos VAL (env)))])
    
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
 (test--> (m Ms)
          (term (f ^ m m))
          (term (-- (clos 1 (env)))))
 (test--> (m Ms)
          (term (f ^ † m))
          (term ((pred string? m) (env) <= m † (-- (clos 1 (env))) f (-- (clos 1 (env))))))
 (test--> (m Ms)
          (term (posn ^ m m))
          (term (-- (clos (s-cons posn 2) (env)))))
 (test--> (m Ms)
          (term (posn? ^ m m))
          (term (-- (clos (s-pred posn) (env)))))
 (test--> (m Ms)
          (term (posn-x ^ m m))
          (term (-- (clos (s-ref posn 0) (env)))))
 (test--> (m Ms)
          (term (posn-y ^ m m))
          (term (-- (clos (s-ref posn 1) (env)))))
 (test--> (m Ms)
          (term (c ^ m m))
          (term (-- (cons (-- (clos 2 (env)))
                          (-- (clos 3 (env))))))))



