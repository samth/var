#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "step.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluation functions

(define (eval_vcΔ P)
  (apply-reduction-relation* (-->_vcΔ (all-but-last P))
                             (last P)))

(define (eval_vcc~Δ P)
  (apply-reduction-relation* (-->_vcc~Δ (all-but-last P))
                             (last P)))

(test-predicate (redex-match λc 
                  [(in-hole 𝓔 (blame h g #f (pred (λ x x)) #f))])
                (eval_vcΔ example-8))