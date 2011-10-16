#lang var

(module prime? racket (provide/contract [prime? (anything -> bool?)]))

(module keygen racket (require (only-in prime? prime?)) (provide/contract [keygen (anything -> prime?)]))

(module rsa racket (require (only-in prime? prime?)) (provide/contract [rsa (prime? -> (string? -> string?))]))

(require (only-in rsa rsa) (only-in keygen keygen))

((rsa (keygen #f)) "Plain")

