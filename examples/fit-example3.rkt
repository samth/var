#lang s-exp "../verified.rkt" ;trace

;(module prime? (any/c -> bool/c) ☁)
(module prime? (any/c -> bool/c) (λ z (if (nat? z) (= z 7) false)))
;(module keygen (any/c -> prime?) ☁) 
(module keygen (any/c -> prime?) (λ e 7)) 

(module rsa ((any/c -> prime?) -> (string/c -> string/c)) ☁)
((rsa keygen) "Plain")

