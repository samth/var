#lang s-exp "../verified.rkt"

(module f (any/c -> (any/c -> any/c)) ☁)
(module g ((pred (λ x x)) -> nat/c) ☁ )
(module h any/c (λ z ((f g) #f)))

(h 0)
         
