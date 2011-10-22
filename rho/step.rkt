#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt"
         "step-v.rkt" "step-c.rkt" "step-m.rkt" "step-e.rkt")
(provide (except-out (all-defined-out) test))
(provide v c m e)
(test-suite test step)

(define (-->_vc∆ Ms)
  (union-reduction-relations e
                             (context-closure (union-reduction-relations v c (m Ms)) λcρ 𝓔)))

(test
 (define Ms 
   (term [(module m racket 
            (require) 
            (define n 7)
            (provide/contract 
             [n (pred exact-nonnegative-integer? m)]))]))
 (test-->> (-->_vc∆ Ms)
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
 (test-->> (-->_vc∆ Ms)
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
 (test-->> (-->_vc∆ Ms)
           (term (clos (@ (fact ^ † f) 5 †) ()))
           (term (-- (clos 120 ())))))


     

;; FIXME TODO
#;
(define (-->_vcc~Δ Ms)
  (union-reduction-relations error-propagate 
                             (context-closure (union-reduction-relations v c c~ (Δ~ Ms)) λc~ 𝓔)))
