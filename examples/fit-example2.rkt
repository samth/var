#lang s-exp "../verified.rkt" ;trace

(module prime? (any/c -> bool/c) ☁)

(module keygen (any/c -> prime?) (λ e 7)) 

(module rsa (prime? -> (string/c -> string/c)) ☁)

((rsa (keygen #f)) "Plain")

