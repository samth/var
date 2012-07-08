#lang racket
(require rackunit)

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

;; contracts
(define c/any `(flat (λ (x Num) #t)))
(define c/prime `(flat (λ (x Num) (prime? x))))
(define c/non-neg `(flat (λ (x Num) (non-neg? x))))

;; expresions
(define ev? '(λ (x Num) (even? x)))
(define od? '(λ (x Num) (odd? x)))
(define db1
  `(mon h f g
        (((flat ,ev?) ↦ (flat ,ev?))
         ↦ ((flat ,ev?) ↦ (flat ,ev?)))
        (λ (f (Num → Num))
          (λ (x Num)
            (f (f x))))))
(define db2 ; like db1, but wrong
  `(mon h f g
        (((flat ,ev?) ↦ (flat ,ev?))
         ↦ ((flat ,ev?) ↦ (flat ,ev?)))
        (λ (f (Num → Num))
          (λ (x Num) 7))))
(define ap0
  `(,db1 (λ (x Num) 2)))
(define ap1
  `(,db1 (λ (x Num) 7)))
(define ap00 `(,ap0 42))
(define ap01 `(,ap0 13))
(define ap10 `(,ap1 0))
(define tri `(μ (f (Num → Num))
                (λ (n Num)
                  (if (zero? n) 0
                      (+ n (f (- n 1)))))))
(define ap00-db2 `((,db2 ,ap0) 0))
(define keygen ; opaque
  `(mon h f g (,c/any ↦ ,c/prime) (• (Num → Num))))
(define rsa ; opaque
  `(mon h f g (,c/prime ↦ (,c/any ↦ ,c/any)) (• (Num → (Num → Num)))))
(define rsa-ap
  `((,rsa (,keygen 13)) (• Num)))
#;(define sqroot
    `(mon h f g (,c/non-neg ↦ ,c/non-neg)
          (λ (x Num) (sqrt x))))
#;(define sqrt-user
    `(mon h f g ((,c/any ↦ ,c/any) ↦ ,c/any)
          (λ (f (Num → Num)) (,sqroot (f 0)))))
#;(define sqrt-ap
    `(,sqrt-user (• (Num → Num))))
(define sum
  `(μ (f ((List Num) → Num))
      (λ (xs (List Num))
        (if (nil? xs) 0 (+ (car xs) (f (cdr xs)))))))
(define range
  `(μ (range (Num → (Num → (List Num))))
      (λ (lo Num)
        (λ (hi Num)
          (if (≤ lo hi)
              (cons lo ((range (+ 1 lo)) hi))
              nil)))))

(define append
  `(μ (append ((List Num) → ((List Num) → (List Num))))
      (λ (xs (List Num))
        (λ (ys (List Num))
          (if (nil? xs) ys
              (cons (car xs)
                    ((append (cdr xs)) ys)))))))

(define filter
  `(μ (filter ((Num → Bool) → ((List Num) → (List Num))))
      (λ (p (Num → Bool))
        (λ (xs (List Num))
          (if (nil? xs) nil
              (if (p (car xs))
                  (cons (car xs) ((filter p) (cdr xs)))
                  ((filter p) (cdr xs))))))))

(define slowsort
  `(μ (sort ((List Num) → (List Num)))
      (λ (xs (List Num))
        (if (nil? xs) nil
            ((,append
              (sort ((,filter (λ (y Num) (≤ y (car xs)))) (cdr xs))))
             (cons (car xs) (sort ((,filter (λ (y Num) (≥ y (car xs)))) (cdr xs)))))))))

;; contract checking for list of even numbers
(define all-even?
  `(μ (all-even? (con (List Num)))
      ((flat (λ (xs (List Num)) (nil? xs)))
       ∨
       (cons/c (flat ,ev?) all-even?))))

;; contract checking for function pairs
(define func-pair?
  `(cons/c ((flat ,ev?) ↦ (flat ,od?))
           ((flat ,od?) ↦ (flat ,ev?))))

;; monitored list of evens
(define even-list-ok
  `(mon h f g ,all-even? (cons 0 (cons 2 nil))))
(define even-list-er
  `(mon h f g ,all-even? (cons 0 (cons 1 nil))))

;; monitored function pairs
(define func-pair-ok ; won't type check b/c current cons is too restricted
  `((cdr (mon h f g ,func-pair? (cons (λ (x Num) (+ x 1))
                                      (λ (x Num) (+ x 1)))))
    1))
(define func-pair-er1 ; won't type check b/c current cons is too restricted
  `((car (mon h f g ,func-pair? (cons (λ (x Num) x) (λ (x Num) x))))
    1))
(define func-pair-er2 ; won't type check b/c current cons is too restricted
  `((cdr (mon h f g ,func-pair? (cons (λ (x Num) x) (λ (x Num) x))))
    1))

;;;;; testing
(define exps (list ev? db1 db2 ap0 ap1 ap00 ap01 ap10 tri ap00-db2))

;; test read/show
(for-each (λ (e)
            (check-equal?
             (read-exp e)
             ((compose read-exp show-exp read-exp) e)))
          exps)
;; test type-checking
(define tc (compose show-type type-check read-exp))
(check-equal? (tc ev?) '(Num → Bool))
(check-equal? (tc db1) '((Num → Num) → (Num → Num)))
(check-equal? (tc ap0) '(Num → Num))
(check-equal? (tc ap00) 'Num)
(check-equal? (tc tri) '(Num → Num))
(check-equal? (tc keygen) '(Num → Num))
(check-equal? (tc rsa) '(Num → (Num → Num)))
(check-equal? (tc rsa-ap) 'Num)
#;(check-equal? (tc sqroot) '(Num → Num))
#;(check-equal? (tc sqrt-user) '((Num → Num) → Num))
#;(check-equal? (tc sqrt-ap) 'Num)
(check-equal? (tc sum) '((List Num) → Num))
(check-equal? (tc range) '(Num → (Num → (List Num))))
(check-equal? (tc append) '((List Num) → ((List Num) → (List Num))))
(check-equal? (tc filter) '((Num → Bool) → ((List Num) → (List Num))))
(check-equal? (tc slowsort) '((List Num) → (List Num)))
(check-equal? (tc even-list-ok) '(List Num))
(check-equal? (tc even-list-er) '(List Num))

;; for debugging
(define (non-det f xs)
  (apply set-union (set-map xs f)))
(define step1 (curry non-det step))
(define (pow f n) (apply compose (make-list n f)))
(define (step* k e) ((pow step1 k) (set (load (read-exp e)))))

;;;;; tests
(check-equal? (eval-cek ev?) {set 'function})
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

;;;;; benchmarks

;; tak, translated from http://www.larcenists.org/R6src/tak.sch
(define tak
  `(μ (tak (Num → (Num → (Num → Num))))
      (λ (x Num)
        (λ (y Num)
          (λ (z Num)
            (if (not (< y x))
                z
                (((tak (((tak (- x 1)) y) z))
                  (((tak (- y 1)) z) x))
                 (((tak (- z 1)) x) y))))))))
#;(time (eval-cek `(((,tak 9) 6) 3)))

;; takl, translated from http://www.larcenists.org/R6src/takl.sch
(define listn
  `(μ (listn (Num → (List Num)))
      (λ (n Num)
        (if (zero? n) nil (cons n (listn (- n 1)))))))
(define mas
  (let ([shorter? `(μ (shorter? ((List Num) → ((List Num) → Bool)))
                      (λ (x (List Num))
                        (λ (y (List Num))
                          (and (not (nil? y))
                               (or (nil? x)
                                   ((shorter? (cdr x)) (cdr y)))))))])
    `(μ (mas ((List Num) → ((List Num) → ((List Num) → (List Num)))))
        (λ (x (List Num))
          (λ (y (List Num))
            (λ (z (List Num))
              (if (not ((,shorter? y) x))
                  z
                  (((mas (((mas (cdr x)) y) z))
                    (((mas (cdr y)) z) x))
                   (((mas (cdr z)) x) y)))))))))
#;(time (eval-cek `(((,mas (,listn 6)) (,listn 4)) (,listn 2))))

;; cpstak, translated from http://www.larcenists.org/R6src/cpstak.sch
(define cpstak
  (let ([tak
         `(μ (tak (Num → (Num → (Num → ((Num → Num) → Num)))))
             (λ (x Num)
               (λ (y Num)
                 (λ (z Num)
                   (λ (k (Num → Num))
                     (if (not (< y x))
                         (k z)
                         ((((tak (- x 1))
                            y)
                           z)
                          (λ (v1 Num)
                            ((((tak (- y 1))
                               z)
                              x)
                             (λ (v2 Num)
                               ((((tak (- z 1))
                                  x)
                                 y)
                                (λ (v3 Num)
                                  ((((tak v1) v2) v3) k)))))))))))))])
    `(λ (x Num)
       (λ (y Num)
         (λ (z Num)
           ((((,tak x) y) z) (λ (a Num) a)))))))
#;(time (eval-cek `(((,cpstak 9) 6) 3)))