#lang racket
(require "../util.rkt")
(provide (all-from-out "../util.rkt"))
(provide test/σ--> test/v-->>)

(require redex/reduction-semantics)
(define-syntax test/σ-->
  (syntax-rules (term) 
    [(test/σ R (term T1) (term T2) ...)
     (test--> R 
              (term (T1 #hash()))
              (term (T2 #hash()))
              ...)]))

(define-syntax test/v-->>
  (syntax-rules (term) 
    [(test/σ R (term T1) (term T2))
     (test-equal 
      (caar (apply-reduction-relation* R (term (T1 #hash()))))
      (term T2))]))