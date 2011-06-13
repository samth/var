#lang s-exp "verified.rkt" trace
;; Binary trees

(define-contract bt/c
  (rec/c X 
         (or/c nat/c
               (cons/c nat/c (cons/c X X)))))

(define-contract node/c
  (cons/c nat/c (cons/c bt/c bt/c)))

;; Accessors
(module num (node/c -> nat/c)
  (λ nd
    (first nd)))

(module left (node/c -> bt/c)
  (λ nd
    (first (rest nd))))

(module right (node/c -> bt/c)
  (λ nd
    (rest (rest nd))))

;; First-order
(module sum (bt/c -> nat/c)
  (λ t
    (if (nat? t)
        t
        (+ (num t)
           (+ (sum (left t))
              (sum (right t)))))))

;; Higher-order
(module map ((nat/c -> nat/c) -> (bt/c -> bt/c))
  (λ f
    (λ t
      (if (nat? t)
          (f t)
          (cons (f (num t))
                (cons ((map f) (left t))
                      ((map f) (right t))))))))

(module n nat/c ☁)
;(left (cons n (cons n n)))
;(sum (cons n (cons n n)))
;=> (-- nat/c)

;(sum (cons 1 (cons 2 3)))
;=> 6

;((map (λ x (+ 1 x))) (cons 1 (cons 2 3)))
;=> (cons 2 (cons 3 4))
 
;((map (λ x n)) (cons 1 (cons 2 3)))
;=> (cons (-- nat/c) (cons (-- nat/c) (-- nat/c)))

;(sum ((map (λ x n)) (cons 1 (cons 2 3))))
;=> (-- nat/c)

;; doesn't work because we haven't got (-- rec/c) yet.
(module bt bt/c ☁)
(sum bt)


;(module c (cons/c nat/c (rec/c X (cons/c X X))) ☁)
;(rest c)
