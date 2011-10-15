#lang s-exp "../verified.rkt" cesk ;-trace


(define/contract p (anything -> (anything -> bool?)) (λ (x) (λ (y) x)))

(define/contract gen (anything -> (λ (z) (pred (λ (x) (z x))))) ☁)

(define/contract gen2 (anything -> (λ (z1) ((pred (λ (x) (z1 x))) -> anything))) ☁)

(require (only-in gen2 gen2) (only-in gen gen) (only-in p p))

((gen2 (p #f)) (gen (p #t)))

