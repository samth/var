#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt"
         "step-v.rkt" "step-c.rkt" 
         "step-m.rkt" "step-e.rkt")
(provide (except-out (all-defined-out) test))
(provide v c m e)
(test-suite test step)

(define (-->_vcme Ms)
  (union-reduction-relations 
   e
   (context-closure (union-reduction-relations v c (m Ms)) λcρ 𝓔)))

(test
 (define Ms 
   (term [(module m racket 
            (require) 
            (define n 7)
            (provide/contract 
             [n (pred exact-nonnegative-integer? m)]))]))
 (test-->> (-->_vcme Ms)
           (term (n ^ † m))
           (term (-- (clos 7 ())))))

(test
 (define Ms 
   ;; Factorial with type-like contract
   (term [(module f racket 
            (require) 
            (define fact 
              (λ ! (n) 
                (if (@ zero? n f) 1
                    (@ * n (@ ! (@ sub1 n f) f) f))))
            (provide/contract 
             [fact ((pred exact-nonnegative-integer? f) 
                    -> (pred exact-nonnegative-integer? f))]))]))
 (test-->> (-->_vcme Ms)
           (term (clos (@ (fact ^ † f) 5 †) ()))
           (term (-- (clos 120 ())))))

(test
 ;; Factorial with simple dependent contract
 (define Ms 
   (term [(module f racket 
            (require) 
            (define fact 
              (λ ! (n) 
                (if (@ zero? n f) 1
                    (@ * n (@ ! (@ sub1 n f) f) f))))
            (provide/contract 
             [fact ((pred exact-nonnegative-integer? f) 
                    ->
                    (λ (x)
                      (and/c (pred exact-nonnegative-integer? f)
                             (pred (λ (y) (@ <= x y f)) f))))]))]))
 (test-->> (-->_vcme Ms)
           (term (clos (@ (fact ^ † f) 5 †) ()))
           (term (-- (clos 120 ())
                     ((pred (λ (y) (@ <= x y f)) f)
                      ((x (-- (clos 5 ())))))))))

(test
 (define Ms
   (term [(module p racket
            (require)
            (struct posn (x y))
            (provide/contract
             [posn ((pred exact-nonnegative-integer? p)
                    (pred exact-nonnegative-integer? p)
                    -> (pred (posn? ^ p p) p))]
             [posn? ((pred (λ (x) #t) p) -> (pred boolean? p))]
             [posn-x ((pred (posn? ^ p p) p) -> (pred exact-nonnegative-integer? p))]
             [posn-y ((pred (posn? ^ p p) p) -> (pred exact-nonnegative-integer? p))]))]))
 
 (test-->> (-->_vcme Ms)
           (term (clos (@ (posn ^ † p) 1 2 †) ()))
           (term (-- (struct posn
                       (-- (clos 1 ()))
                       (-- (clos 2 ())))
                     ((pred (posn? ^ p p) p) ()))))
 (test-->> (-->_vcme Ms)
           (term (clos (@ (posn? ^ † p)
                          (@ (posn ^ † p) 1 2 †)
                          †)
                       ()))
           (term (-- (clos #t ()))))
 (test-->> (-->_vcme Ms)
           (term (clos (@ (posn-x ^ † p)
                          (@ (posn ^ † p) 1 2 †)
                          †)
                       ()))
           (term (-- (clos 1 ()))))
 (test-->> (-->_vcme Ms)
           (term (clos (@ (posn-y ^ † p)
                          (@ (posn ^ † p) 1 2 †)
                          †)
                       ()))
           (term (-- (clos 2 ())))))
 
           
 
           
                



     

;; FIXME TODO
#;
(define (-->_vcc~Δ Ms)
  (union-reduction-relations error-propagate 
                             (context-closure (union-reduction-relations v c c~ (Δ~ Ms)) λc~ 𝓔)))
