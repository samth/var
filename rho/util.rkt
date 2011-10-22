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

(test-suite test util)
