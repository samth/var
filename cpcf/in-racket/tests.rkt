#lang racket
(require rackunit)

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

;; contracts
(define c/any `(flat (λ (x) #t)))
(define c/list `(μ (list?) ((flat nil?) ∨ (cons/c ,c/any list?))))
(define c/num-list `(μ (num-list?) ((flat nil?) ∨ (cons/c (flat num?) num-list?))))
(define c/even-list `(μ (evens?) ((flat nil?) ∨ (cons/c (flat even?) evens?))))

;; db1 example from section 2
(define modl-db
  `(module db (((flat even?) ↦ (flat even?)) ↦ ((flat even?) ↦ (flat even?)))
     (λ (f) (λ (x) (f (f x))))))
(define prog-db00
  `(,modl-db
    (module f ,c/any (λ (x) 2))
    ((db f) 42)))
(define prog-db01
  `(,modl-db
    (module f ,c/any (λ (x) 2))
    ((db f) 13)))
(define prog-db10
  `(,modl-db
    (module f ,c/any (λ (x) 7))
    ((db f) 0)))
(define prog-db00-2
  `((module db (((flat even?) ↦ (flat even?)) ↦ ((flat even?) ↦ (flat even?)))
      (λ (f) (λ (x) 7)))
    (module f ,c/any (λ (x) 2))
    ((db f) 42)))
(check-equal? (eval-cek prog-db00) {set 2})
(check-equal? (eval-cek prog-db01) {set '(blame † db)})
(check-equal? (eval-cek prog-db10) {set '(blame † db)})
(check-equal? (eval-cek prog-db00-2) {set '(blame db db)}) 

;; computes factorial
(define (prog-factorial n)
  `((module fac ((flat int?) ↦ (flat int?))
      (μ (fac) (λ (n) (if (zero? n) 1 (* n (fac (- n 1)))))))
    (fac ,n)))
(check-equal? (eval-cek (prog-factorial 3)) {set 6})
#;(check-equal? (eval-cek (prog-factorial '•)) {set '• '(blame † fac)}) ; won't terminate

;; rsa example from section 3.4
(define prog-rsa
  `((module keygen (,c/any ↦ (flat prime?)) •)
    (module rsa ((flat prime?) ↦ (,c/any ↦ ,c/any)) •)
    ((rsa (keygen 0)) "Plaintext")))
;; TODO test prog-rsa

;; list functions
(define modl-foldr
  `(module foldr ((,c/any ,c/any ↦ ,c/any) ,c/any ,c/list ↦ ,c/any)
     (μ (foldr)
        (λ (f a xs)
          (if (nil? xs) a
              (f (car xs) (foldr f a (cdr xs))))))))
(define modl-foldl
  `(module foldl ((,c/any ,c/any ↦ ,c/any) ,c/any ,c/list ↦ ,c/any)
     (μ (foldl)
        (λ (f a xs)
          (if (nil? xs) a
              (foldl f (f a (car xs)) (cdr xs)))))))
(define modl-map
  `(module map ((,c/any ↦ ,c/any) ,c/list ↦ ,c/list)
     (λ (f xs)
       (foldr (λ (x ys) (cons (f x) ys)) nil xs))))
(define modl-filter
  `(module filter ((,c/any ↦ (flat bool?)) ,c/list ↦ ,c/list)
     (λ (p xs)
       (foldr (λ (x ys) (if (p x) (cons x ys) ys)) nil xs))))
(define modl-append
  `(module append (,c/list ,c/list ↦ ,c/list)
     (λ (xs ys)
       (foldr cons ys xs))))
(define modl-range
  `(module range ((flat num?) (flat num?) ↦ ,c/num-list)
     (μ (range)
        (λ (lo hi)
          (if (≤ lo hi)
              (cons lo (range (+ 1 lo) hi))
              nil)))))
(define modl-sum
  `(module sum (,c/num-list ↦ (flat num?))
     (λ (xs)
       (foldl + 0 xs))))
(define modl-sorted?
  `(module sorted? (,c/num-list ↦ (flat bool?))
     (μ (sorted?)
        (λ (xs)
          (or (nil? xs)
              (nil? (cdr xs))
              (and (≤ (car xs) (car (cdr xs)))
                   (sorted? (cdr xs))))))))

;; insertion sort example from section 1
(define prog-ins-sort
  `(,modl-sorted?
    (module insert ((flat num?) (,c/num-list ∧ (flat sorted?)) ↦ (,c/num-list ∧ (flat sorted?))) •)
    (module nums ,c/num-list •)
    ,modl-foldl
    (module sort (,c/num-list ↦ (,c/num-list ∧ (flat sorted?)))
      (λ (l)
        (foldl insert nil l)))
    (sort nums)))
(check-equal? (eval-cek prog-ins-sort) {set '•})

;; 'quick'sort
(define prog-qsort
  `(,modl-foldr
    ,modl-range
    ,modl-append
    ,modl-filter
    ,modl-sorted?
    (module sort (,c/num-list ↦ (,c/num-list ∧ (flat sorted?)))
      (μ (sort)
         (λ (xs)
           (if (nil? xs) nil
               (append
                (sort (filter (λ (y) (< y (car xs))) (cdr xs)))
                (cons (car xs)
                      (sort (filter (λ (y) (≥ y (car xs))) (cdr xs)))))))))
    (sort (append (range 8 10) (range 1 3)))))
(check-equal? (eval-cek prog-qsort)
              {set '(cons 1 (cons 2 (cons 3 (cons 8 (cons 9 (cons 10 nil))))))})

;; monitored list of evens
(define prog-even-list-ok
  `((module evens ,c/even-list (cons 0 (cons 2 nil)))
    (car evens)))
(define prog-even-list-err
  `((module evens ,c/even-list (cons 0 (cons 1 nil)))
    (car evens)))
(check-equal? (eval-cek prog-even-list-ok) {set 0})
(check-equal? (eval-cek prog-even-list-err) {set '(blame evens evens)})

;; contract checking for function pairs
(define c/func-pair
  `(cons/c ((flat even?) ↦ (flat even?))
           ((flat odd?) ↦ (flat even?))))
;; monitored function pairs
(define prog-func-pair-ok
  `((module func-pair ,c/func-pair
      (cons (λ (x) (+ x 1)) (λ (x) (+ x 1))))
    ((cdr func-pair) 1)))
(define prog-func-pair-err1
  `((module func-pair ,c/func-pair
      (cons (λ (x) x) (λ (x) x)))
    ((car func-pair) 1)))
(define prog-func-pair-err2
  `((module func-pair ,c/func-pair
      (cons (λ (x) x) (λ (x) x)))
    ((cdr func-pair) 1)))
(check-equal? (eval-cek prog-func-pair-ok) {set 2})
(check-equal? (eval-cek prog-func-pair-err1) {set '(blame † func-pair)})
(check-equal? (eval-cek prog-func-pair-err2) {set '(blame func-pair func-pair)})

;; 'flatten' example from Wright paper, section 1.1
(define modl-flatten
  (let ([c/flat-list
         `(μ (flat-list?)
             ((flat nil?)
              ∨ ; TODO: add 'not' combinator for contract?
              (cons/c ((flat num?) ∨ ((flat bool?) ∨ (flat string?)))
                      flat-list?)))])
    `(module flatten (,c/any ↦ ,c/flat-list)
       (μ (flatten)
          (λ (l)
            (if (nil? l) nil
                (if (cons? l) (append (flatten (car l)) (flatten (cdr l)))
                    (cons l nil))))))))
(define modl-flatten-a
  `(module a (cons/c (flat num?) (cons/c (cons/c (flat num?) (flat nil?))
                                         (cons/c (flat num?) (flat nil?))))
     (cons 1 (cons (cons 2 nil) (cons 3 nil)))))
(define modl-flatten-b
  `(module b ,c/num-list (flatten a)))
(define prog-flatten-ok1 `(,modl-foldr
                           ,modl-flatten
                           ,modl-append
                           ,modl-flatten-a
                           ,modl-flatten-b
                           b))
(check-equal? (eval-cek prog-flatten-ok1)
              {set '(cons 1 (cons 2 (cons 3 nil)))})
(define prog-flatten-ok2 `(,modl-foldr
                           ,modl-flatten
                           ,modl-append
                           ,modl-flatten-a
                           ,modl-flatten-b
                           (car b)))
(check-equal? (eval-cek prog-flatten-ok2) {set 1})
(define prog-flatten-err1 `(,modl-foldr
                            ,modl-map
                            ,modl-flatten
                            ,modl-append
                            ,modl-flatten-a
                            ,modl-flatten-b
                            (map (λ (x) (+ 1 x)) a)))
(check-equal? (eval-cek prog-flatten-err1) {set '(blame † +)})
(define prog-flatten-err2
  `(,modl-foldr
    ,modl-map
    ,modl-flatten 
    ,modl-append
    ,modl-flatten-a
    ,modl-flatten-b
    (map (λ (x) (- x 1))
         (flatten (cons "this" (cons (cons "that" nil) nil))))))
(check-equal? (eval-cek prog-flatten-err2) {set '(blame † -)})

;; taut from Wright paper, section 5.1
(define modl-taut
  (let ([T? `(λ (x) (and (true? x) (not (proc? x))))]
        [F? 'false?])
    `(module taut (,c/any ↦ ,c/any)
       (μ (taut)
          (λ (b)
            (if (,T? b) #t
                (if (,F? b) #f
                    (and (taut (b #t)) (taut (b #f))))))))))
(define prog-taut-a
  `(,modl-taut (taut #t)))
(define prog-taut-b
  `(,modl-taut (taut not)))
(define prog-taut-c
  `(,modl-taut (taut (λ (x) (λ (y) (and x y))))))
(check-equal? (eval-cek prog-taut-a) {set #t})
(check-equal? (eval-cek prog-taut-b) {set #f})
(check-equal? (eval-cek prog-taut-c) {set #f})

;; benchmarks
(define tak ; translated from http://www.larcenists.org/R6src/tak.sch
  `((module tak ((flat int?) (flat int?) (flat int?) ↦ (flat int?))
      (μ (tak)
         (λ (x y z)
           (if (not (< y x))
               z
               (tak (tak (- x 1) y z)
                    (tak (- y 1) z x)
                    (tak (- z 1) x y))))))
    (tak 3 2 1)))
(time (eval-cek tak))

(define takl ; translated from http://www.larcenists.org/R6src/takl.sch
  `((module listn ((flat num?) ↦ ,c/num-list)
      (μ (listn) (λ (n)
                   (if (zero? n) nil (cons n (listn (- n 1)))))))
    (module shorter? (,c/num-list ,c/num-list ↦ (flat bool?))
      (μ (shorter?)
         (λ (x y)
           (and (not (nil? y))
                (or (nil? x)
                    (shorter? (cdr x) (cdr y)))))))
    (module mas (,c/num-list ,c/num-list ,c/num-list ↦ ,c/num-list)
      (μ (mas)
         (λ (x y z)
           (if (not (shorter? y x))
               z
               (mas (mas (cdr x) y z)
                    (mas (cdr y) z x)
                    (mas (cdr z) x y))))))
    (mas (listn 3) (listn 2) (listn 1))))
(time (eval-cek takl))

(define cpstak ; translated from http://www.larcenists.org/R6src/cpstak.sch
  `((module tak
      ((flat num?) (flat num?) (flat num?) ((flat num?) ↦ (flat num?)) ↦ (flat num?))
      (μ (tak)
         (λ (x y z k)
           (if (not (< y x))
               (k z)
               (tak (- x 1)
                    y
                    z
                    (λ (v1)
                      (tak (- y 1)
                           z
                           x
                           (λ (v2)
                             (tak (- z 1)
                                  x
                                  y
                                  (λ (v3)
                                    (tak v1 v2 v3 k)))))))))))
    (module cpstak ((flat num?) (flat num?) (flat num?) ↦ (flat num?))
      (λ (x y z)
        (tak x y z (λ (a) a))))
    (cpstak 3 2 1)))
(time (eval-cek cpstak))

;; test read/show
(for-each
 (λ (p)
   (check-equal?
    (read-prog p)
    ((compose read-prog show-prog read-prog) p)))
 (list prog-db00 prog-db01 prog-db10 prog-db00-2
       (prog-factorial '•) prog-rsa prog-ins-sort prog-qsort
       prog-even-list-ok prog-even-list-err
       prog-func-pair-ok prog-func-pair-err1 prog-func-pair-err2
       prog-flatten-ok1 prog-flatten-ok2 prog-flatten-err1 prog-flatten-err2
       prog-taut-a prog-taut-b prog-taut-c
       tak takl cpstak))

;; for debugging
(define (non-det f xs)
  (apply set-union (set-map xs f)))
(define step1 (curry non-det step))
(define (pow f n) (apply compose (make-list n f)))
(define (step* k e) ((pow step1 k) (set (load (read-exp e)))))
