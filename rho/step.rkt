#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt"
         "step-v.rkt" "step-c.rkt" "step-c-abs.rkt"
         "step-m.rkt" "step-m-abs.rkt" "step-e.rkt"
         "step-a.rkt")
(provide (except-out (all-defined-out) test))
(provide v c c~ m m~ e a)
(test-suite test step)

(define step-count 0)

(define (-->_vcme Ms) 
  (define r 
    (union-reduction-relations v c c~ a (m Ms) (m~ Ms)))    
  (reduction-relation 
   λcρ #:domain (D σ) ;; runs faster if you use REDEX
   (--> ((in-hole 𝓔 REDEX) σ)
        ((in-hole 𝓔 D_contractum) σ_1)
        (where (any_0 ... (any_name (D_contractum σ_1)) any_1 ...)
               ,(let ([r (apply-reduction-relation/tag-with-names r (term (REDEX σ)))])
                  (set! step-count (add1 step-count))                  
                  #;(when (zero? (modulo step-count 50))
                      (printf "steps: ~a, terms: ~a\n" step-count (length r))
                      #;
                      (when (not (null? r))
                        (displayln (first r))))
                  r))
        (computed-name (term any_name))
        redex!)
   (--> (D σ)
        (BLAME σ)
        (where (any_0 ... (any_name (BLAME σ)) any_1 ...)
               ,(apply-reduction-relation/tag-with-names e (term (D σ))))
        (computed-name (term any_name))
        blame!)))

(test
 (define Ms 
   (term [(module m racket 
            (require) 
            (define n 7)
            (provide/contract 
             [n (pred exact-nonnegative-integer? m)]))]))
 (test/v-->> (-->_vcme Ms)
             (term (n ^ † m))
             (term (-- (↓ 7 (env))))))


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
 (test/v-->> (-->_vcme Ms)
             (term (↓ (@ (fact ^ † f) 5 †) (env)))
             (term (-- (↓ 120 (env))))))


;; FIXME -- this is hard to express without GC.
#; 
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
 (test/v-->> (-->_vcme Ms)
             (term (↓ (@ (fact ^ † f) 5 †) (env)))
             (term (-- (↓ 120 (env))
                       ((pred (λ (y) (@ <= x y f)) f)
                        (env (x (-- (↓ 5 (env))))))))))

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
 
 (test/v-->> (-->_vcme Ms)
             (term (↓ (@ (posn ^ † p) 1 2 †) (env)))
             (term (-- (struct posn
                         (-- (↓ 1 (env)))
                         (-- (↓ 2 (env))))
                       ((pred (posn? ^ p p) p) (env)))))
 (test/v-->> (-->_vcme Ms)
             (term (↓ (@ (posn? ^ † p)
                         (@ (posn ^ † p) 1 2 †)
                         †)
                      (env)))
             (term (-- (↓ #t (env)))))
 (test/v-->> (-->_vcme Ms)
             (term (↓ (@ (posn-x ^ † p)
                         (@ (posn ^ † p) 1 2 †)
                         †)
                      (env)))
             (term (-- (↓ 1 (env)))))
 (test/v-->> (-->_vcme Ms)
             (term (↓ (@ (posn-y ^ † p)
                         (@ (posn ^ † p) 1 2 †)
                         †)
                      (env)))
             (term (-- (↓ 2 (env))))))
