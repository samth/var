#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide e)
(test-suite test step-e)

;; when we get blame, discard the context
(define e
  (reduction-relation 
   λcρ #:domain D
   ;; if we reduce to blame, we halt the program
   (--> (in-hole 𝓔 BLAME) BLAME
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
 (test--> e
          (term (@ (blame f f (-- (clos 0 ())) 
                          ((pred exact-nonnegative-integer? f) ())
                          (-- (clos 5 ())))
                   (clos (@ string? 3 †) ())
                   †))
          (term (blame f f (-- (clos 0 ())) 
                       ((pred exact-nonnegative-integer? f) ())
                       (-- (clos 5 ()))))))
 