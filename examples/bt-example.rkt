#lang var ;cesk
;; Binary trees

(define-contract nat/c exact-nonnegative-integer?)

(define-contract bt/c
  (rec/c X 
         (or/c nat/c
               (cons/c nat/c (cons/c X X)))))

(define-contract node/c
  (cons/c nat/c (cons/c bt/c bt/c)))

;; Accessors
(define/contract num (-> node/c nat/c)
  (λ (nd)
    (first nd)))

(define/contract left (-> node/c bt/c)
  (λ (nd)
    (first (rest nd))))

(define/contract right (-> node/c bt/c)
  (λ (nd)
    (rest (rest nd))))

;; First-order
(module sum  racket
  (require 'left 'right 'num)
  (define sum (λ (t)
    (if (exact-nonnegative-integer? t)
        t
        (+ (num t)
           (+ (sum (left t))
              (sum (right t)))))))
  (provide/contract [sum (-> bt/c nat/c)]))

;; Higher-order
(module map racket
  (require 'left 'right 'num)
  (define map 
    (λ (f t)
      (if (exact-nonnegative-integer? t)
          (f t)
          (cons (f (num t))
                (cons (map f (left t))
                      (map f (right t)))))))
  (provide/contract [map (-> (-> nat/c nat/c) bt/c bt/c)]))

(module n racket (provide/contract [n nat/c]))
(module bt racket (provide/contract [bt bt/c]))
;(left (cons n (cons n n)))
;(sum (cons n (cons n n)))
;=> (-- nat/c)

;(sum (cons 1 (cons 2 3)))
;=> 6

;(map (λ (x) (+ 1 x)) (cons 1 (cons 2 3)))
;(map (λ (x) (+ 1 x)) 7)
;=> (cons 2 (cons 3 4))
 
;((map (λ x n)) (cons 1 (cons 2 3)))
;=> (cons (-- nat/c) (cons (-- nat/c) (-- nat/c)))

;(sum ((map (λ x n)) (cons 1 (cons 2 3))))
;=> (-- nat/c)

;; doesn't work because we haven't got (-- rec/c) yet.

(require 'sum 'bt)
(sum bt)


;(module c (cons/c nat/c (rec/c X (cons/c X X))) ☁)
;(rest c)
