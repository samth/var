#lang s-exp "../verified.rkt"

(module prime? (anything -> bool?) ☁)

(module keygen (anything -> prime?) ☁) 

(module rsa (prime? -> (string? -> string?)) ☁)

((rsa (keygen #f)) "Plain")

