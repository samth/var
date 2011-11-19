#lang var rho
;;--------------------------------------------------------------------
;; Dependent contract example, infeasible blame
(module opaque racket
  (provide/contract [n exact-nonnegative-integer?]))

(module id racket
  (define (f x) x)
  (provide/contract
   [f (exact-nonnegative-integer? 
       . -> . 
       (λ (x)
         (pred (λ (y) (= y x)))))]))

(require 'opaque 'id)
(f n)