#lang s-exp "verified.rkt"

(module prime? (anything -> bool?) ☁)

(module keygen (anything -> (pred prime?)) ☁) 

(module rsa ((pred prime?) -> (string? -> string?)) ☁)

((rsa (keygen #f)) "Plain")

