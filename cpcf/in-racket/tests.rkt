#lang racket
(require rackunit)

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

;; contracts
(define c/any `(flat (λ (x) #t)))
(define c/prime `(flat prime?))
(define c/non-neg `(flat non-neg?))
(define c/list `(μ (list?) ((flat nil?) ∨ (cons/c ,c/any list?))))
(define c/num-list `(μ (num-list?) ((flat nil?) ∨ (cons/c (flat num?) num-list?))))
(define c/even-list `(μ (evens?) ((flat nil?) ∨ (cons/c (flat even?) evens?))))

;; expresions
(define db-ap00
  `((module db (((flat even?) ↦ (flat even?)) ↦ ((flat even?) ↦ (flat even?)))
      (λ (f) (λ (x) (f (f x)))))
    (module f ,c/any (λ (x) 2))
    ((db f) 42)))
(define db-ap01
  `((module db (((flat even?) ↦ (flat even?)) ↦ ((flat even?) ↦ (flat even?)))
      (λ (f) (λ (x) (f (f x)))))
    (module f ,c/any (λ (x) 2))
    ((db f) 13)))
(define db-ap10
  `((module db (((flat even?) ↦ (flat even?)) ↦ ((flat even?) ↦ (flat even?)))
      (λ (f) (λ (x) (f (f x)))))
    (module f ,c/any (λ (x) 7))
    ((db f) 0)))
(define db-ap00-2
  `((module db (((flat even?) ↦ (flat even?)) ↦ ((flat even?) ↦ (flat even?)))
      (λ (f) (λ (x) 7)))
    (module f ,c/any (λ (x) 2))
    ((db f) 42)))
(define fac-ap ; TODO: (μ ...) is not V
  `((module fac ((flat int?) ↦ (flat int?)) (μ (fac) (λ (n) (if (zero? n) 1 (* n (fac (- n 1)))))))
    (fac 3)))
(define rsa-ap
  `((module keygen (,c/any ↦ ,c/prime) •)
    (module rsa (,c/prime ↦ (,c/any ↦ ,c/any)) •)
    ((rsa (keygen 13)) 42)))
#;(define sqroot
    `(mon h f g (,c/non-neg ↦ ,c/non-neg)
          (λ (x Num) (sqrt x))))
#;(define sqrt-user
    `(mon h f g ((,c/any ↦ ,c/any) ↦ ,c/any)
          (λ (f (Num → Num)) (,sqroot (f 0)))))
#;(define sqrt-ap
    `(,sqrt-user (• (Num → Num))))
(define sort-ap
  `((module sum (,c/num-list ↦ (flat int?))
      (μ (f)
         (λ (xs)
           (if (nil? xs) 0 (+ (car xs) (f (cdr xs)))))))
    (module range ((flat int?) ↦ ((flat int?) ↦ ,c/num-list))
      (μ (range)
         (λ (lo)
           (λ (hi)
             (if (≤ lo hi)
                 (cons lo ((range (+ 1 lo)) hi))
                 nil)))))
    (module append (,c/list ↦ (,c/list ↦ ,c/list))
      (μ (append)
         (λ (xs)
           (λ (ys)
             (if (nil? xs) ys
                 (cons (car xs)
                       ((append (cdr xs)) ys)))))))
    (module filter ((,c/any ↦ (flat bool?)) ↦ (,c/list ↦ ,c/list))
      (μ (filter)
         (λ (p)
           (λ (xs)
             (if (nil? xs) nil
                 (if (p (car xs))
                     (cons (car xs) ((filter p) (cdr xs)))
                     ((filter p) (cdr xs))))))))
    (module sort (,c/num-list ↦ ,c/num-list)
      (μ (sort)
         (λ (xs)
           (if (nil? xs) nil
               ((append
                 (sort ((filter (λ (y) (≤ y (car xs)))) (cdr xs))))
                (cons (car xs) (sort ((filter (λ (y) (≥ y (car xs)))) (cdr xs)))))))))
    
    (sort ((append ((range 8) 10)) ((range 1) 3)))))

;; monitored list of evens
(define even-list-ok
  `((module evens ,c/even-list (cons 0 (cons 2 nil)))
    (car evens)))
(define even-list-er
  `((module evens ,c/even-list (cons 0 (cons 1 nil)))
    (car evens)))

;; contract checking for function pairs
(define c/func-pair
  `(cons/c ((flat even?) ↦ (flat even?))
           ((flat odd?) ↦ (flat even?))))
;; monitored function pairs
(define func-pair-ok
  `((module func-pair ,c/func-pair
      (cons (λ (x) (+ x 1)) (λ (x) (+ x 1))))
    ((cdr func-pair) 1)))
(define func-pair-er1
  `((module func-pair ,c/func-pair
      (cons (λ (x) x) (λ (x) x)))
    ((car func-pair) 1)))
(define func-pair-er2
  `((module func-pair ,c/func-pair
      (cons (λ (x) x) (λ (x) x)))
    ((cdr func-pair) 1)))

;; benchmarks
(define tak ; translated from http://www.larcenists.org/R6src/tak.sch
  `((module tak ((flat int?) ↦ ((flat int?) ↦ ((flat int?) ↦ (flat int?))))
      (μ (tak)
         (λ (x)
           (λ (y)
             (λ (z)
               (if (not (< y x))
                   z
                   (((tak (((tak (- x 1)) y) z))
                     (((tak (- y 1)) z) x))
                    (((tak (- z 1)) x) y))))))))
    (((tak 3) 2) 1)))

(define takl ; translated from http://www.larcenists.org/R6src/takl.sch
  `((module listn ((flat num?) ↦ ,c/num-list)
      (μ (listn) (λ (n)
                   (if (zero? n) nil (cons n (listn (- n 1)))))))
    (module shorter? (,c/num-list ↦ (,c/num-list ↦ (flat bool?)))
      (μ (shorter?)
         (λ (x) (λ (y)
                  (and (not (nil? y))
                       (or (nil? x)
                           ((shorter? (cdr x)) (cdr y))))))))
    (module mas (,c/num-list ↦ (,c/num-list ↦ (,c/num-list ↦ ,c/num-list)))
      (μ (mas)
         (λ (x) (λ (y) (λ (z)
                         (if (not ((shorter? y) x))
                             z
                             (((mas (((mas (cdr x)) y) z))
                               (((mas (cdr y)) z) x))
                              (((mas (cdr z)) x) y))))))))
    (((mas (listn 3)) (listn 2)) (listn 1))))

(define cpstak ; translated from http://www.larcenists.org/R6src/cpstak.sch
  `((module tak
      ((flat num?) ↦ ((flat num?) ↦ ((flat num?) ↦ (((flat num?) ↦ (flat num?)) ↦ (flat num?)))))
      (μ (tak)
         (λ (x)
           (λ (y)
             (λ (z)
               (λ (k)
                 (if (not (< y x))
                     (k z)
                     ((((tak (- x 1))
                        y)
                       z)
                      (λ (v1)
                        ((((tak (- y 1))
                           z)
                          x)
                         (λ (v2)
                           ((((tak (- z 1))
                              x)
                             y)
                            (λ (v3)
                              ((((tak v1) v2) v3) k))))))))))))))
    (module cpstak ((flat num?) ↦ ((flat num?) ↦ ((flat num?) ↦ (flat num?))))
      (λ (x) (λ (y) (λ (z)
                      ((((tak x) y) z) (λ (a) a))))))
    (((cpstak 3) 2) 1)))

;;;;; testing
(define progs
  (list db-ap00 db-ap01 db-ap10 db-ap00-2 fac-ap func-pair-ok func-pair-er1 tak takl cpstak))

;; test read/show
(for-each (λ (p)
            (check-equal?
             (read-prog p)
             ((compose read-prog show-prog read-prog) p)))
          progs)

;; for debugging
(define (non-det f xs)
  (apply set-union (set-map xs f)))
(define step1 (curry non-det step))
(define (pow f n) (apply compose (make-list n f)))
(define (step* k e) ((pow step1 k) (set (load (read-exp e)))))

;;;;; tests
(check-equal? (eval-cek db-ap00) {set 2})
(check-equal? (eval-cek db-ap01) {set '(blame † db)})
(check-equal? (eval-cek db-ap00-2) {set '(blame db db)}) 
(check-equal? (eval-cek fac-ap) {set 6})
#;(check-equal? (eval-cek rsa-ap) {set `• `(blame f h)})
#;(check-equal? (eval-cek sqrt-ap) {set '• '(blame g h)})
(check-equal? (eval-cek sort-ap) {set '(cons 1 (cons 2 (cons 3 (cons 8 (cons 9 (cons 10 nil))))))})
#;(check-equal? (eval-cek `((,filter (• (Num → Bool))) (cons 1 (cons 2 nil))))
                ;; every possible subsequence
                {set 'nil '(cons 1 nil) '(cons 2 nil) '(cons 1 (cons 2 nil))})
#;(check-equal? (eval-cek `(,slowsort (• (List Num))))
                ;; won't terminate, kont keeps growing
                {set '(• (List Num))})
(check-equal? (eval-cek even-list-ok) {set 0})
(check-equal? (eval-cek even-list-er) {set '(blame evens evens)})
(check-equal? (eval-cek func-pair-ok) {set 2})
(check-equal? (eval-cek func-pair-er1) {set '(blame † func-pair)})
(check-equal? (eval-cek func-pair-er2) {set '(blame func-pair func-pair)})

(time (eval-cek tak))
(time (eval-cek takl))
(time (eval-cek cpstak))