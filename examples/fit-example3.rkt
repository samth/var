#lang s-exp "../verified.rkt" ;trace

;(module prime? (any/c -> bool/c) ☁)
(module prime? (any/c -> bool/c) (λ z (if (nat? z) (= z 7) false)))
;(module keygen (any/c -> (pred prime?)) ☁) 
(module keygen (any/c -> (pred prime?)) (λ e 7)) 

(module rsa ((any/c -> (pred prime?)) -> (string/c -> string/c)) ☁)
((rsa keygen) "Plain")

