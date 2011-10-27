#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide m)
(test-suite test step-m)

(define (m Ms)
  (reduction-relation
   λcρ #:domain D
   (--> (X_1 ^ X X)
        (close VAL)
        (where VAL (lookup-modref/val X X_1 ,Ms))
        m-self)
   (--> (X_1 ^ LAB X)
        (CON () <= X LAB (close VAL) X_1 (close VAL))
        (where CON (lookup-modref/con X X_1 ,Ms))
        (where VAL (lookup-modref/val X X_1 ,Ms))        
        (side-condition (not (eq? (term X) (term LAB))))
        m-other)))

(define-metafunction λcρ
  close : VAL -> D
  [(close (cons VAL_1 VAL_2))
   (-- (cons (close VAL_1)
             (close VAL_2)))]
  [(close VAL)
   (-- (clos VAL ()))])
    
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
          (term (-- (clos 1 ()))))
 (test--> (m Ms)
          (term (f ^ † m))
          (term ((pred string? m) () <= m † (-- (clos 1 ())) f (-- (clos 1 ())))))
 (test--> (m Ms)
          (term (posn ^ m m))
          (term (-- (clos (s-cons posn 2) ()))))
 (test--> (m Ms)
          (term (posn? ^ m m))
          (term (-- (clos (s-pred posn) ()))))
 (test--> (m Ms)
          (term (posn-x ^ m m))
          (term (-- (clos (s-ref posn 0) ()))))
 (test--> (m Ms)
          (term (posn-y ^ m m))
          (term (-- (clos (s-ref posn 1) ()))))
 (test--> (m Ms)
          (term (c ^ m m))
          (term (-- (cons (-- (clos 2 ()))
                          (-- (clos 3 ())))))))



