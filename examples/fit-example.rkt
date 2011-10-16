#lang var

(module prime? racket (provide/contract [prime? (-> anything boolean?)]))

(module keygen racket (require (only-in prime? prime?)) (provide/contract [keygen (-> anything prime?)]))

(module rsa racket (require (only-in prime? prime?)) (provide/contract [rsa (-> prime? (-> string? string?))]))

(require rsa keygen)

((rsa (keygen #f)) "Plain")

