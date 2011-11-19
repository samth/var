#lang var rho
;;--------------------------------------------------------------------
;; Simple H.O. counterexample
;; Map got the wrong contract
(module opaque racket
  (provide/contract
   [f (string? . -> . string?)]
   [los (listof string?)]))

(module map racket
  (define (map f ls)
    (if (empty? ls) ls
        (cons (f (car ls))
              (map f (cdr ls)))))
  (provide/contract
   [map ((any/c . -> . any/c) 
         (listof any/c) 
         . -> .
         (listof boolean?))]))

(require 'opaque 'map)

(map f los) 