#lang s-exp "verified.rkt" ;trace

(module prime? (any/c -> bool/c) ☁)

(module keygen (any/c -> (pred prime?)) (λ e 7)) 

(module rsa ((pred prime?) -> (string/c -> string/c)) ☁)

((rsa (keygen #f)) "Plain")

