#lang racket/load

;; An example from Degen, Thiemann, Wehr

;; Aside: there's an interesting interaction between contracts and
;; laziness in this example:
;; the domain contract is strict in *both* its arguments, while
;; the function is only strict in the first.

;; So with in a lazy language, contract monitoring is semantics changing.

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