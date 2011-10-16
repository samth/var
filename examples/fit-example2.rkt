#lang var ;trace

(define/contract prime? (any? -> bool?) ☁)

(module keygen racket   
  (require (only-in prime? prime?))
  (define keygen (λ (e) 7))
  (provide/contract [keygen (anything -> prime?)])) 

(module rsa racket (require (only-in prime? prime?)) (provide/contract [rsa (prime? -> (string? -> string?))]))
(require (only-in rsa rsa) (only-in keygen keygen))
((rsa (keygen #f)) "Plain")

