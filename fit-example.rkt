#lang s-exp "verified.rkt"

(module prime? (any/c -> bool/c) ☁)
(module keygen (any/c -> (pred prime?)) ☁)
(module rsa ((pred prime?) -> (string/c -> string/c)) ☁)

((rsa (keygen #f)) "Plain")