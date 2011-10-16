#lang var ;trace

;(module prime? (-> any/c bool/c) ☁)
(define/contract prime? (-> any? bool?) (λ (z) (if (exact-nonnegative-integer? z) (= z 7) false)))
;(module keygen (-> any/c prime?) ☁) 
(module keygen racket
  (require (only-in prime? prime?)) 
  (define keygen (λ (e) 7))
  (provide/contract [keygen (-> any? prime?)]))

(module rsa racket 
  (require (only-in prime? prime?))
  (provide/contract [rsa (-> (-> any? prime?) (-> string? string?))]))
(require (only-in rsa rsa) (only-in keygen keygen))
((rsa keygen) "Plain")

