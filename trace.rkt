#lang racket
(require redex)
(require "lang.rkt" "test.rkt" "step.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trace and stepper

(define-syntax-rule (trace-it R P)
  (traces (R (all-but-last P))
          (last P)
          #:pred colorize))

(define (colorize x)
  (cond [(redex-match λc~ V x) "green"]
        [(redex-match λc~ (blame ★ f V_0 C V_1) x) "pink"]
        [(redex-match λc~ B x) "red"]
        [else #t]))

(define-syntax-rule (step-it R P)
  (stepper (R (all-but-last P))
           (last P)))

(trace-it -->_vcc~Δ fit-example)
;(trace-it -->_vcc~Δ fit-example-rsa-7)
;(trace-it -->_vcc~Δ fit-example-keygen-string)
;(step-it -->_vcc~Δ fit-example)


#;
(traces (-->_vcΔ (all-but-last example-8))
        (last example-8))
#;
(traces (-->_vcc~Δ (all-but-last example-8-opaque))
        (last example-8-opaque))


