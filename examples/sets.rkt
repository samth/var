#lang var rho
;;--------------------------------------------------------------------
;; Representing (infinite) sets with predicates
;; Tricky dependent contract
(module opaque racket
  (provide/contract 
   [f (any/c . -> . boolean?)]
   [g (any/c . -> . boolean?)]
   [a any/c]))

(module set racket
  (define (intersect s t)
    (λ (x)
      (and (s x)
           (t x))))
  
  (provide/contract 
   [intersect
    ((any/c . -> . boolean?)
     (any/c . -> . boolean?)
     . -> . 
     (λ (s t)
       (any/c 
        . -> . 
        ;; r implies x in s and t
        (λ (x) (pred (λ (r) (or (not r) (and (s x) (t x)))))))))]))


(require 'set)
((intersect f g) a)