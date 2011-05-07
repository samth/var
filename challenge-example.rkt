#lang racket/load

;; An example from Degen, Thiemann, Wehr
(module m racket
  (define f (λ (p) (car p)))
  
  (define carg
    (and/c 
     (flat-contract ; Type
      (λ (x) 
        (and (pair? x)
             (integer? (car x))
             (integer? (cdr x)))))
          
     (flat-contract ; Contract
      (λ (p) 
        (match p
          [(cons x y) (and (> x y) (>= y 0))])))))
    
  (define cres
    (and/c (flat-contract ; Type
            integer?)            
           (flat-contract ; Contract
            (λ (r) (> r 0)))))
  
  (provide/contract [f (-> carg cres)]))
  
;; Prove the implementation of f meets its specification.