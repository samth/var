#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test op)

(define-metafunction λcρ
  op-con : OP -> CON
  [(op-con OP?) ((∧) -> (pred boolean? Λ))]
  [(op-con natural*->natural)
   ((rec/c X (or/c (atom/c empty Λ) (cons/c (pred exact-nonnegative-integer? Λ) X)))
    ->* (pred exact-nonnegative-integer? Λ))]
  [(op-con natural-natural*->natural)
   ((pred exact-nonnegative-integer? Λ)
    (rec/c X (or/c (atom/c empty Λ) (cons/c (pred exact-nonnegative-integer? Λ) X)))
    ->* (pred exact-nonnegative-integer? Λ))]
  [(op-con natural-natural->natural) 
   ((pred exact-nonnegative-integer? Λ)
    (pred exact-nonnegative-integer? Λ)
    -> (pred exact-nonnegative-integer? Λ))]
  [(op-con quotient)
   ((pred exact-nonnegative-integer? Λ)
    (and/c (pred exact-nonnegative-integer? Λ)
           (not/c (pred zero? Λ)))
    -> (pred exact-nonnegative-integer? Λ))]
  [(op-con random)
   ((and/c (pred exact-nonnegative-integer? Λ)
           (not/c (pred zero? Λ)))
    -> (pred exact-nonnegative-integer? Λ))]  
  [(op-con natural->natural)
   ((pred exact-nonnegative-integer? Λ)
    -> (pred exact-nonnegative-integer? Λ))]
  [(op-con car) ((pred cons? Λ) -> (∧))]
  [(op-con cdr) ((pred cons? Λ) -> (∧))]
  [(op-con natural-natural->bool)
   ((pred exact-nonnegative-integer? Λ)
    (pred exact-nonnegative-integer? Λ)
    -> (pred boolean? Λ))]
  [(op-con char-char->bool)
   ((pred char? Λ)
    (pred char? Λ)
    -> (pred boolean? Λ))]
  [(op-con string-string->bool)
   ((pred string? Λ)
    (pred string? Λ)
    -> (pred boolean? Λ))]
  [(op-con procedure-arity-includes?)
   ((pred procedure? Λ) 
    (pred exact-nonnegative-integer? Λ) 
    -> (pred boolean? Λ))]
  [(op-con cons)
   ((∧) (∧) -> (pred cons? Λ))]
  [(op-con eqv?)
   ((∧) (∧) -> (pred boolean? Λ))]
  [(op-con symbol=?)
   ((pred symbol? Λ) (pred symbol? Λ) -> (pred boolean? Λ))]
  [(op-con (s-pred X_1 X_2)) (∧)]  ;; Already taken care of.
  [(op-con (s-cons X_1 X_2 natural)) (∧)]
  [(op-con (s-ref X_1 X_2 natural)) (∧)])

(test
 (redex-check λcρ OP (term (op-con OP))))