#lang racket
(require "../loader.rkt" "../run.rkt" "../meta.rkt" "../cesk.rkt" "../util.rkt")
(require redex/reduction-semantics)
(test-suite test factorial)

(define fact-program
  (load-program "../examples/factorial.rkt"))

(test
 (define reduction-results 
   (apply set (eval-it ---> fact-program)))
   
 (test-equal reduction-results
             (set (term ((-- ((pred exact-nonnegative-integer? Λ) (env))) (sto)))
                  (term ((-- (clos 1 (env))) (sto)))))
 
 (test-equal (apply set (CESK-run fact-program))
             reduction-results))
