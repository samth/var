#lang var rho
;;--------------------------------------------------------------------
;; Simple first-order infeasible blame
(module opaque racket
  (provide/contract
   [n exact-nonnegative-integer?]))

(require 'opaque)
(quotient 1 (add1 n))