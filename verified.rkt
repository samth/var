#lang racket
(require "trace.rkt" "annotate.rkt" redex/reduction-semantics)
(require (for-syntax syntax/parse))
(provide #%module-begin #%top-interaction)

(define-syntax (#%module-begin stx)
  (syntax-parse stx
    [(_ m ... e)
     #'(#%plain-module-begin (trace-it -->_vcc~Δ (term (ann [m ... e]))))]))