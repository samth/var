#lang s-exp "../verified.rkt" ;trace

(define/contract b bool? •)
(define/contract n nat? •)
(define/contract c (cons/c nat? nat?) •)
(define/contract g (zero? -> nat?) •)
(define/contract f ((nat? -> nat?) -> bool?) •)
(define/contract q (any? -> any?) •)
(define/contract p proc? •)

(define/contract zo? (any? -> bool?)
  (λ (x)
    (if (nat? x)
        (if (zero? x)
            #t
            (if (= x 1)
                #t
                #f))
        #f)))

(module czo racket
  (require (only-in zo? zo?))
  (provide/contract [czo (cons/c zo? zo?)]))

(module zo->zo racket 
  (require (only-in zo? zo?))
  (define zo->zo (λ (y) y))
  (provide/contract [zo->zo (zo? -> zo?)]))

(module z->z racket 
  (require (only-in zo? zo?))
  (define z->z (λ (v) v))
  (provide/contract [z->z ((and/c zero? zo?) -> (or/c zero? zo?))]))

(require (only-in zo? zo?))

(zo? 7)

;n
;(if b 7 "fred")
;(add1 n)
;(proc? g)
;(g 7)
;(g n)
;(q q)
;(first c)
;(rest c)
;(f (λ (h) (zero? (h 5))))
;(zo->zo 7)
;(q zo?)
;(add1 (if b 7 8))
;(first b)
