#lang s-exp "../verified.rkt"

(module prime? racket (provide/contract [prime? (anything -> bool?)]))

(module keygen racket (provide/contract [keygen (anything -> prime?)]))

(module rsa racket (provide/contract [rsa (prime? -> (string? -> string?))]))

(require (only-in rsa rsa) (only-in keygen keygen))

((rsa (keygen #f)) "Plain")

