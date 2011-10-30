#lang var rho trace ;cesk ;trace


(define/contract p (-> any/c (-> any/c boolean?)) (λ (x) (λ (y) x)))

(define/contract gen (-> any/c (λ (z) (pred (λ (x) (z x))))) •)

(define/contract gen2 (-> any/c (λ (z1) (-> (pred (λ (x) (z1 x))) any/c))) •)

(require (only-in gen2 gen2) (only-in gen gen) (only-in p p))

((gen2 (p #f)) (gen (p #t)))

