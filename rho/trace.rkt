#lang racket
(require redex/reduction-semantics racket/pretty unstable/pretty)
(require "lang.rkt" "examples.rkt" "step.rkt" "annotate.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test trace)

(provide -->_vcme)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trace and stepper

(define-syntax-rule (trace-it R P . rest)
  (traces (R (program-modules P))
          `(clos ,(last P) ())
          #:pred (colorize (program-modules P))
          . rest))

(define ((colorize Ms) x node)
  (define opaques 
    (filter-map (λ (M) 
                  (match M
                    [(list 'module n lang (list 'define _ •) ... prov) n]
                    [_ #f]))
                Ms))
  (cond [(redex-match λcρ V x) "green"]
        [(redex-match λcρ BLAME x)
         (redex-let λcρ
                    ([(blame LAB any_0 V any_1 V_0) x])
                    (cond [(equal? (term LAB) '★) "pink"]
                          [(member (term LAB) opaques) "pink"]
                          [else "red"]))]
        [(null? (term-node-children node)) "blue"]
        [else #t]))

(define-syntax-rule (step-it R P)
  (stepper (R (program-modules P))
           (last P)))
