#lang racket
(require redex/reduction-semantics)
(require "lang.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples and tests

;; Modified from Figure 8 in paper (8 -> #f).
(define example-8
  (term [(module f (any/c -> (any/c -> any/c)) (λ x x))
         (module g ((pred (λ x x)) -> int/c) (λ x 0))
         (module h any/c (λ z (((f ^ h) (g ^ h) h) #f h)))
         ((h ^ †) 0 †)]))

(define example-8-opaque
  (term [(module f (any/c -> (any/c -> any/c)) ☁)
         (module g ((pred (λ x x)) -> int/c) ☁)
         (module h any/c (λ z (((f ^ h) (g ^ h) h) #f h)))
         ((h ^ †) 0 †)]))

(test-predicate (redex-match λc-user M) (first example-8))
(test-predicate (redex-match λc-user M) (second example-8))
(test-predicate (redex-match λc-user M) (third example-8))
(test-predicate (redex-match λc-user E) (last example-8))
(test-predicate (redex-match λc~ P) example-8-opaque)
(test-predicate (redex-match λc-user P) example-8)
(test-predicate (redex-match λc P) example-8)
(test-predicate (redex-match λc~ P) example-8)

(test-predicate (redex-match λc-user C) (term ((pred (λ x x)) -> int/c)))

(define fit-example
  (term [(module prime? (int/c -> any/c) ☁)
         (module rsa ((pred (prime? ^ rsa)) -> (string/c -> string/c)) ☁)
         (module keygen (any/c -> (pred (prime? ^ keygen))) ☁)
         (((rsa ^ †) ((keygen ^ †) #f †) †) "Plain" †)]))

(define fit-example-rsa-7
  (term [(module prime? (int/c -> any/c) ☁)
         (module rsa ((pred (prime? ^ rsa)) -> (string/c -> string/c)) ☁)
         (module keygen (any/c -> (pred (prime? ^ keygen))) (λ x 7))
         (((rsa ^ †) ((keygen ^ †) #f †) †) "Plain" †)]))

;; Should see keygen break contract with prime?.
(define fit-example-keygen-string
  (term [(module prime? (int/c -> any/c) ☁)
         (module rsa ((pred (prime? ^ rsa)) -> (string/c -> string/c)) ☁)
         (module keygen (any/c -> (pred (prime? ^ keygen))) (λ x "Key"))
         (((rsa ^ †) ((keygen ^ †) #f †) †) "Plain" †)]))

(define fit-example-alt
  (term [(module prime? (int/c -> any/c) ☁)
         (module rsa (string/c -> ((pred (prime? ^ rsa)) -> string/c)) ☁)
         (module keygen (any/c -> (pred (prime? ^ keygen))) ☁)
         (((rsa ^ †) "Plain" †) ((keygen ^ †) #f †) †)]))

(test-predicate (redex-match λc~ P) fit-example)
(test-predicate (redex-match λc~ P) fit-example-alt)