#lang var rho eval
(module m racket
  (define f (λ (n . r) (+ n n (apply + r))))
  (provide/contract [f ((exact-nonnegative-integer?) 
                        #:rest (listof exact-nonnegative-integer?) 
                        . ->* . 
                        exact-nonnegative-integer?)]))
(require 'm)
(f 2 3 4) ;=> 11