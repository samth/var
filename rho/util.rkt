#lang racket
(require "../util.rkt")
(provide (all-from-out "../util.rkt"))
(provide test/σ-->)

(require redex/reduction-semantics)
(define-syntax test/σ-->
  (syntax-rules (term) 
    [(test/σ R (term T1) (term T2) ...)
     (test--> R 
              (term (T1 #hash()))
              (term (T2 #hash()))
              ...)]))