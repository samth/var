#lang s-exp "verified.rkt" cesk-trace


(module p (anything -> (anything -> bool?)) (λ (x) (λ (y) x)))

(module gen (anything -> (λ (z) (pred (λ (x) (z x))))) ☁)

(module gen2 (anything -> (λ (z1) ((pred (λ (x) (z1 x))) -> anything))) ☁)

((gen2 (p #f)) (gen (p #t)))

