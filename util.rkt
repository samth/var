#lang racket
(provide (except-out (all-defined-out) test))
(require redex/reduction-semantics)

(define-syntax-rule (test-suite test suite)
  (begin (define test-thunk (box test-results))
	 (provide suite)
	 (define (suite) ((unbox test-thunk)))
	 (define-syntax-rule (test e (... ...))
	   (set-box! test-thunk
		     (let ((rest (unbox test-thunk)))
		       (lambda ()
			 e (... ...) (rest)))))))

(define-syntax-rule (traces . args) ((dynamic-require 'redex 'traces) . args))
(define-syntax-rule (stepper . args) ((dynamic-require 'redex 'stepper) . args))
(define (term-node-children . args)
  (apply (dynamic-require 'redex 'term-node-children) args))

(define current-exact? (make-parameter #t))

;; handles the second arg not being symbols
(define (variables-not-in* a bs)
  (variables-not-in a (map (λ (b) (if (symbol? b) b 'loc)) bs)))

(test-suite test util)
