#lang racket
(require rackunit)

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

;; contracts
(define c/any `(flat (λ (x) #t)))
(define c/prime `(flat prime?))
(define c/non-neg `(flat non-neg?))

;; expresions
(define db1
  `(mon h f g
        (((flat even?) ↦ (flat even?))
         ↦ ((flat even?) ↦ (flat even?)))
        (λ (f)
          (λ (x) (f (f x))))))
(define db2 ; like db1, but wrong
  `(mon h f g
        (((flat even?) ↦ (flat even?))
         ↦ ((flat even?) ↦ (flat even?)))
        (λ (f) (λ (x) 7))))
(define ap0 `(,db1 (λ (x) 2)))
(define ap1 `(,db1 (λ (x) 7)))
(define ap00 `(,ap0 42))
(define ap01 `(,ap0 13))
(define ap10 `(,ap1 0))
(define tri `(μ (f)
                (λ (n)
                  (if (zero? n) 0
                      (+ n (f (- n 1)))))))
(define ap00-db2 `((,db2 ,ap0) 0))
(define keygen ; opaque
  `(mon h f g (,c/any ↦ ,c/prime) •))
(define rsa ; opaque
  `(mon h f g (,c/prime ↦ (,c/any ↦ ,c/any)) •))
(define rsa-ap
  `((,rsa (,keygen 13)) •))
#;(define sqroot
    `(mon h f g (,c/non-neg ↦ ,c/non-neg)
          (λ (x Num) (sqrt x))))
#;(define sqrt-user
    `(mon h f g ((,c/any ↦ ,c/any) ↦ ,c/any)
          (λ (f (Num → Num)) (,sqroot (f 0)))))
#;(define sqrt-ap
    `(,sqrt-user (• (Num → Num))))
(define sum
  `(μ (f)
      (λ (xs)
        (if (nil? xs) 0 (+ (car xs) (f (cdr xs)))))))
(define range
  `(μ (range)
      (λ (lo)
        (λ (hi)
          (if (≤ lo hi)
              (cons lo ((range (+ 1 lo)) hi))
              nil)))))

(define append
  `(μ (append)
      (λ (xs)
        (λ (ys)
          (if (nil? xs) ys
              (cons (car xs)
                    ((append (cdr xs)) ys)))))))

(define filter
  `(μ (filter)
      (λ (p)
        (λ (xs)
          (if (nil? xs) nil
              (if (p (car xs))
                  (cons (car xs) ((filter p) (cdr xs)))
                  ((filter p) (cdr xs))))))))

(define slowsort
  `(μ (sort)
      (λ (xs)
        (if (nil? xs) nil
            ((,append
              (sort ((,filter (λ (y) (≤ y (car xs)))) (cdr xs))))
             (cons (car xs) (sort ((,filter (λ (y) (≥ y (car xs)))) (cdr xs)))))))))

;; contract checking for list of even numbers
(define all-even?
  `(μ (all-even?)
      ((flat (λ (xs) (nil? xs)))
       ∨
       (cons/c (flat even?) all-even?))))

;; contract checking for function pairs
(define func-pair?
  `(cons/c ((flat even?) ↦ (flat even?))
           ((flat odd?) ↦ (flat even?))))

;; monitored list of evens
(define even-list-ok
  `(mon h f g ,all-even? (cons 0 (cons 2 nil))))
(define even-list-er
  `(mon h f g ,all-even? (cons 0 (cons 1 nil))))

;; monitored function pairs
(define func-pair-ok ; won't type check b/c current cons is too restricted
  `((cdr (mon h f g ,func-pair? (cons (λ (x) (+ x 1))
                                      (λ (x) (+ x 1)))))
    1))
(define func-pair-er1 ; won't type check b/c current cons is too restricted
  `((car (mon h f g ,func-pair? (cons (λ (x) x) (λ (x) x))))
    1))
(define func-pair-er2 ; won't type check b/c current cons is too restricted
  `((cdr (mon h f g ,func-pair? (cons (λ (x) x) (λ (x) x))))
    1))

;;;;; testing
(define exps (list db1 db2 ap0 ap1 ap00 ap01 ap10 tri ap00-db2))

;; test read/show
(for-each (λ (e)
            (check-equal?
             (read-exp e)
             ((compose read-exp show-exp read-exp) e)))
          exps)

;; for debugging
(define (non-det f xs)
  (apply set-union (set-map xs f)))
(define step1 (curry non-det step))
(define (pow f n) (apply compose (make-list n f)))
(define (step* k e) ((pow step1 k) (set (load (read-exp e)))))

;;;;; tests
(check-equal? (eval-cek ap00) {set 2})
(check-equal? (eval-cek ap01) {set `(blame g h)})
(check-equal? (eval-cek `(,tri 3)) {set 6})
(check-equal? (eval-cek rsa-ap) {set `• `(blame f h)})
#;(check-equal? (eval-cek sqrt-ap) {set '• '(blame g h)})
(check-equal? (eval-cek `((,range 1) 3)) {set '(cons 1 (cons 2 (cons 3 nil)))})
(check-equal? (eval-cek `(,sum ((,range 0) 10))) {set 55})
(check-equal? (eval-cek `((,filter (• (Num → Bool))) (cons 1 (cons 2 nil))))
              ;; every possible subsequence
              {set 'nil '(cons 1 nil) '(cons 2 nil) '(cons 1 (cons 2 nil))})
(check-equal? (eval-cek `((,append ((,range 1) 3)) ((,range 4) 6)))
              (eval-cek `((,range 1) 6)))
(check-equal? (eval-cek `(,slowsort (cons 3 (cons 2 (cons 4 (cons 1 nil))))))
              {set '(cons 1 (cons 2 (cons 3 (cons 4 nil))))})
#;(check-equal? (eval-cek `(,slowsort (• (List Num))))
                ;; won't terminate, kont keeps growing
                {set '(• (List Num))})
(check-equal? (eval-cek even-list-ok) {set '(cons 0 (cons 2 nil))})
(check-equal? (eval-cek even-list-er) {set '(blame f h)})
(check-equal? (eval-cek func-pair-ok) {set 2})
(check-equal? (eval-cek func-pair-er1) {set '(blame g h)})
(check-equal? (eval-cek func-pair-er2) {set '(blame f h)})

;; benchmarks
(define tak
  `(μ (tak)
      (λ (x)
        (λ (y)
          (λ (z)
            (if (not (< y x))
                z
                (((tak (((tak (- x 1)) y) z))
                  (((tak (- y 1)) z) x))
                 (((tak (- z 1)) x) y))))))))
(define tak-ap `(((,tak 9) 6) 3))
(time (eval-cek tak-ap))