#lang racket
(provide (except-out (all-defined-out) test)
         traces stepper initial-char-width term-node-children reduction-steps-cutoff)
(require redex/reduction-semantics unstable/lazy-require)
(lazy-require [redex (traces stepper initial-char-width term-node-children reduction-steps-cutoff)])

(define-syntax-rule (test-suite test suite)
  (begin (define test-thunk (box test-results))
	 (provide suite)
	 (define (suite) ((unbox test-thunk)))
	 (define-syntax-rule (test e (... ...))
	   (set-box! test-thunk
		     (let ((rest (unbox test-thunk)))
		       (λ ()
			 e (... ...) (rest)))))))

(define current-exact? (make-parameter #t))

;; handles the second arg not being symbols
(define (variables-not-in* a bs)
  (variables-not-in a (map (λ (b) (if (symbol? b) b 'loc)) bs)))

(test-suite test util)

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