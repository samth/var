#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide e)
(test-suite test step-e)

;; when we get blame, discard the context
(define e
  (reduction-relation 
   λcρ #:domain (D σ)
   ;; if we reduce to blame, we halt the program
   (--> ((in-hole 𝓔 BLAME) σ) (BLAME σ)
        (side-condition (not (equal? (term hole) (term 𝓔))))
        halt-blame)
     
   ;; FIXME TODO
   #;
   ;; normalize abstract values at the end to make testing easier
   (--> V V_norm
        (where V_norm (normalize V))
        (side-condition (not (equal? (term V) (term V_norm))))
        normalize-abstract)))

(test
 (test/σ--> e
            (term (@ (blame f f (-- (↓ 0 (env))) 
                            ((pred exact-nonnegative-integer? f) (env))
                            (-- (↓ 5 (env))))
                     (↓ (@ string? 3 †) (env))
                     †))
            (term (blame f f (-- (↓ 0 (env))) 
                         ((pred exact-nonnegative-integer? f) (env))
                         (-- (↓ 5 (env)))))))
