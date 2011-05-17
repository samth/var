#lang s-exp "verified.rkt"

(module f (any/c -> (any/c -> any/c)) (λ x x))
(module g ((pred (λ x x)) -> nat/c) (λ x 0))
(module h any/c (λ z ((f g) #f)))

(h 0)
         
