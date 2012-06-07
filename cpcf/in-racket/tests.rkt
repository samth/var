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

;; for debugging
#;(define step1 (curry non-det step))
#;(define (pow f n) (apply compose (make-list n f)))
#;(define (step* k e) ((pow step1 k) (set (load (read-exp e)))))

;;;;; tests
(check-equal? (eval-cek ev?) {set 'function})
(check-equal? (eval-cek ap00) {set 2})
(check-equal? (eval-cek ap01) {set `(blame g h)})
(check-equal? (eval-cek `(,tri 3)) {set 6})
(check-equal? (eval-cek rsa-ap) {set `• `(blame f h)})
#;(check-equal? (eval-cek sqrt-ap) {set '• '(blame g h)})
(check-equal? (eval-cek `(,sum ((,range 0) 10))) {set 55})