#lang racket
(require rackunit)

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

;; contracts
(define c/any `(flat (λ (x) #t)))
(define c/list `(μ (list?) (or/c (flat nil?) (cons/c ,c/any list?))))
(define c/num-list `(μ (num-list?) (or/c (flat nil?) (cons/c (flat num?) num-list?))))
(define c/even-list `(μ (evens?) (or/c (flat nil?) (cons/c (flat even?) evens?))))

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
#;(define prog-rsa
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
    (module insert ((flat num?) (and/c ,c/num-list (flat sorted?)) ↦ (and/c ,c/num-list (flat sorted?))) •)
    (module nums ,c/num-list •)
    ,modl-foldl
    (module sort (,c/num-list ↦ (and/c ,c/num-list (flat sorted?)))
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
    (module sort (,c/num-list ↦ (and/c ,c/num-list (flat sorted?)))
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
             (or/c (flat nil?)
                   ; TODO: add 'not' combinator for contract?
                   (cons/c (or/c (flat num?) (or/c (flat bool?) (flat string?)))
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
(define (prog-taut p)
  (let ([T? `(λ (x) (and (true? x) (not (proc? x))))]
        [F? 'false?])
    `((module taut (,c/any ↦ ,c/any)
        (μ (taut)
           (λ (b)
             (if (,T? b) #t
                 (if (,F? b) #f
                     (and (taut (b #t)) (taut (b #f))))))))
      (taut ,p))))
(check-equal? (eval-cek (prog-taut #t)) {set #t})
(check-equal? (eval-cek (prog-taut 'not)) {set #f})
(check-equal? (eval-cek (prog-taut '(λ (x) (λ (y) (and x y))))) {set #f})

;; 'member' from Wright paper Appendix
(define (prog-member x l)
  `((module member (,c/any ,c/list ↦ ,c/list)
      (μ (member)
         (λ (x l)
           (if (nil? l) nil
               (if (equal? x (car l)) l
                   (member x (cdr l)))))))
    (member ,x ,l)))
(check-equal? (eval-cek (prog-member 3 '(cons 2 (cons 3 (cons 5 nil)))))
              {set '(cons 3 (cons 5 nil))})
(check-equal? (eval-cek (prog-member '• '(cons 2 (cons 3 (cons 5 nil)))))
              ; every possible tail
              {set '(cons 2 (cons 3 (cons 5 nil)))
                   '(cons 3 (cons 5 nil)) '(cons 5 nil) 'nil})

;; 'lastpair' from Wright paper Appendix
(define (prog-lastpair s)
  `((module lastpair ((cons/c ,c/any ,c/list) ↦ (cons/c ,c/any (flat nil?)))
      (μ (lastpair)
         (λ (s)
           (if (cons? (cdr s))
               (lastpair (cdr s))
               s))))
    (lastpair ,s)))
(check-equal? (eval-cek (prog-lastpair '(cons 1 (cons 2 nil)))) {set '(cons 2 nil)})
(check-equal? (eval-cek (prog-lastpair 'nil)) {set '(blame † lastpair)})
(check-equal? (eval-cek (prog-lastpair '•)) {set '• '(blame † lastpair)}) ; TODO crash

;; subst* from Wright paper Appendix
(define (prog-subst* new old t)
  `((module subst* (,c/any ,c/any ,c/any ↦ ,c/any)
      (μ (subst*)
         (λ (new old t)
           (if (equal? old t) new
               (if (cons? t) (cons (subst* new old (car t))
                                   (subst* new old (cdr t)))
                   t)))))
    (subst* ,new ,old ,t)))
(check-equal? (eval-cek (prog-subst* '42 '(cons 2 nil) '(cons 1 (cons (cons 2 nil) (cons 2 nil)))))
              {set '(cons 1 (cons 42 42))})

;; 'Y' + 'last' from Wright paper Appendix
(define prog-last
  `((module Y ,c/any #|TODO|#
      (λ (f)
        (λ (y)
          (((λ (x) (f (λ (z) ((x x) z))))
            (λ (x) (f (λ (z) ((x x) z)))))
           y))))
    (module last (,c/list ↦ ,c/any)
      (Y (λ (f)
           (λ (x)
             (if (nil? (cdr x))
                 (car x)
                 (f (cdr x)))))))
    (last (cons 1 (cons 2 nil)))))
(check-equal? (eval-cek prog-last) {set 2})

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

;; rsa example translated from
;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/rsa.scm
(define prog-rsa
  `((module extended-gcd ((flat int?) (flat int?) ↦ (cons/c (flat int?) (flat int?)))
      (μ (ext-gcd)
         (λ (a b)
           (if (zero? (mod a b))
               (cons 0 1)
               (let* ([x:y (ext-gcd b (mod a b))]
                      [x (car x:y)]
                      [y (cdr x:y)])
                 (cons y (- x (* y (quot a b)))))))))
    (module modulo-inverse ((flat int?) (flat int?) ↦ (flat int?))
      (λ (a n)
        (mod (car (extended-gcd a n)) n)))
    (module totient ((flat int?) (flat int?) ↦ (flat int?))
      (λ (p q)
        (* (- p 1) (- q 1))))
    (module square ((flat int?) ↦ (flat int?))
      (λ (x) (* x x)))
    (module modulo-power ((flat int?) (flat int?) (flat int?) ↦ (flat int?))
      (μ (mod-pow)
         (λ (base exp n)
           (if (= exp 0) 1
               (if (odd? exp)
                   (mod (* base (mod-pow base (- exp 1) n)) n)
                   (mod (square (mod-pow base (/ exp 2) n)) n))))))
    (module legal-public-exponent?
      ((flat int?) (flat int?) (flat int?) ↦ (flat bool?))
      (λ (e p q)
        (and (< 1 e)
             (< e (totient p q))
             (= 1 (gcd e (totient p q))))))
    (module private-exponent
      ((flat int?) (flat int?) (flat int?) ↦ (or/c (flat int?) (flat false?)))
      (λ (e p q)
        (if (legal-public-exponent? e p q)
            (modulo-inverse e (totient p q))
            #f)))
    (module encrypt
      ((flat int?) (flat int?) (flat int?) ↦ (or/c (flat int?) (flat false?)))
      (λ (m e n)
        (if (> m n) #f
            (modulo-power m e n))))
    (module decrypt
      ((flat int?) (flat int?) (flat int?) ↦ (flat int?))
      (λ (c d n)
        (modulo-power c d n)))
    
    (let* ([p 41] ; "large" prime
           [q 47] ; "large" prime
           [n (* p q)] ; public modulus
           [e 7] ; public exponent
           [d (private-exponent e p q)] ; private exponent
           [plaintext 42]
           [ciphertext (encrypt plaintext e n)]
           [decrypted-ciphertext (decrypt ciphertext d n)])
      (= plaintext decrypted-ciphertext))))
(check-equal? (eval-cek prog-rsa) {set #t})


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
       (prog-taut '•)
       tak takl cpstak))

;; for debugging
(define step1 (curry non-det step))
(define (pow f n) (apply compose (make-list n f)))
(define (step* k e) ((pow step1 k) (set (load (read-exp e)))))
