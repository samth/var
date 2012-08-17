#lang racket
(require rackunit)

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

;; db1 example from section 2
(define (prog-db db f x)
  `((module db
      (provide
       [db (((flat even?) ↦ (flat even?)) ↦ ((flat even?) ↦ (flat even?)))])
      (define db ,db))
    (require db)
    ((db ,f) ,x)))
(define db-right '(λ (f) (λ (x) (f (f x)))))
(define db-wrong '(λ (f) (λ (x) 7)))
(check-equal? (eval-cek (prog-db db-right '(λ (x) 2) 42)) {set 2})
(check-equal? (eval-cek (prog-db db-right '(λ (x) 2) 13)) {set '(blame † db)})
(check-equal? (eval-cek (prog-db db-right '(λ (x) 7) 42)) {set '(blame † db)})
(check-equal? (eval-cek (prog-db db-wrong '(λ (x) 2) 42)) {set '(blame db db)}) 

;; computes factorial
(define (prog-fac n)
  `((module fac
      (provide
       [fac ((flat nat?) ↦ (flat nat?))])
      (define (fac n)
        (if (zero? n) 1
            (* n (fac (- n 1))))))
    (require fac)
    (fac ,n)))
(define (prog-fac-tc n)
  `((module fac
      (provide
       [fac ((flat nat?) ↦ (flat nat?))])
      (define (fac n)
        (fac-helper n 1))
      (define (fac-helper n acc)
        (if (zero? n) acc
            (fac-helper (- n 1) (* acc n)))))
    (require fac)
    (fac ,n)))
(check-equal? (eval-cek (prog-fac 3)) {set 6})
(check-equal? (eval-cek (prog-fac '•)) {set '• '(blame † fac)})
(check-equal? (eval-cek (prog-fac-tc 3)) {set 6})
(check-equal? (eval-cek (prog-fac-tc '•)) {set '• '(blame † fac)})

;; rsa example from section 3.4
#;(define prog-rsa
    `((module keygen (,c/any ↦ (flat prime?)) •)
      (module rsa ((flat prime?) ↦ (,c/any ↦ ,c/any)) •)
      ((rsa (keygen 0)) "Plaintext")))
;; TODO test prog-rsa

;; list functions
(define modl-list
  `(module list
     (provide
      [foldr ((,c/any ,c/any ↦ ,c/any) ,c/any ,c/list ↦ ,c/any)]
      [foldl ((,c/any ,c/any ↦ ,c/any) ,c/any ,c/list ↦ ,c/any)]
      [filter
       ((,c/any ↦ ,c/any) ,c/list ↦ (λ (p xs)
                                      (μ (all?)
                                         (or/c (flat nil?)
                                               (cons/c (flat p) all?)))))]
      [filter-tc
       ((,c/any ↦ ,c/any) ,c/list ↦ (λ (p xs)
                                      (μ (all?)
                                         (or/c (flat nil?)
                                               (cons/c (flat p) all?)))))]
      [map ((,c/any ↦ ,c/any) ,c/list ↦ ,c/list)]
      [map-tc ((,c/any ↦ ,c/any) ,c/list ↦ ,c/list)]
      [reverse (,c/list ↦ ,c/list)]
      [append (,c/list ,c/list ↦ ,c/list)]
      [range ((flat int?) (flat int?) ↦ ,c/int-list)]
      [length (,c/list ↦ (flat nat?))]
      [length-tc (,c/list ↦ (flat nat?))])
     
     (define (foldr f a xs)
       (cond
         [(nil? xs) a]
         [else (f (car xs) (foldr f a (cdr xs)))]))
     
     (define (foldl f a xs)
       (cond
         [(nil? xs) a]
         [else (foldl f (f (car xs) a) (cdr xs))]))
     
     (define (filter p xs)
       (foldr (λ (x zs) (if (p x) (cons x zs) zs)) nil xs))
     
     (define (filter-tc p xs)
       (reverse (foldl (λ (x zs) (if (p x) (cons x zs) zs)) nil xs)))
     
     (define (map f xs)
       (foldr (λ (x zs) (cons (f x) zs)) nil xs))
     
     (define (map-tc f xs)
       (reverse (foldl (λ (x zs) (cons (f x) zs)) nil xs)))
     
     (define (reverse xs)
       (foldl cons nil xs))
     
     (define (append xs ys)
       (foldr cons ys xs))
     
     (define (range lo hi)
       (if (> lo hi) nil
           (cons lo (range (+ 1 lo) hi))))
     
     (define (length xs)
       (foldr (λ (_ n) (+ 1 n)) 0 xs))
     
     (define (length-tc xs)
       (foldl (λ (_ n) (+ 1 n)) 0 xs))))

;; TODO: currently need to bind intermediate results to variables to help
;; the evaluator remember passed tests
(define defn-sorted?
  `(define (sorted? xs)
     (cond
       [(nil? xs) #t]
       [else (let ([zs (cdr xs)])
               (cond
                 [(nil? zs) #t]
                 [else (and (≤ (car xs) (car zs)) (sorted? zs))]))])))

;; insertion sort example from section 1
#;(define prog-ins-sort
    `(,modl-sorted?
      (module insert ((flat real?) (and/c ,c/real-list (flat sorted?)) ↦ (and/c ,c/real-list (flat sorted?))) •)
      (module nums ,c/real-list •)
      ,modl-foldl
      (module sort (,c/real-list ↦ (and/c ,c/real-list (flat sorted?)))
        (λ (l)
          (foldl insert nil l)))
      (sort nums)))
#;(check-equal? (eval-cek prog-ins-sort) {set '• 'nil})

;; 'length' from section 4.4
(define (prog-length l)
  `(,modl-list
    (require list)
    (length ,l)))
(define (prog-length-tc l)
  `(,modl-list
    (require list)
    (length-tc ,l)))
(check-equal? (eval-cek (prog-length '(cons 1 (cons 2 nil)))) {set 2})
(check-equal? (eval-cek (prog-length '•)) {set '(blame † list) '•})
(check-equal? (eval-cek (prog-length-tc '(cons 1 (cons 2 nil)))) {set 2})
#;(check-equal? (eval-cek (prog-length-tc '•)) {set '(blame † list) '•}) ; FIXME won't terminate, needs widening

;; 'filter'
(define (prog-filter p xs)
  `(,modl-list
    (require list)
    (filter ,p ,xs)))
(define (prog-filter-tc p xs)
  `(,modl-list
    (require list)
    (filter-tc ,p ,xs)))
(check-equal? (eval-cek (prog-filter 'even? '(range 1 4))) {set '(cons 2 (cons 4 nil))})
(check-equal? (eval-cek (prog-filter '• '(range 1 2))) ; every possible subsequence
              {set '(blame † list) '(blame † ∆) '(blame † car) '(blame † cdr)
                   '(cons 1 (cons 2 nil)) '(cons 1 nil) '(cons 2 nil) 'nil})
(check-equal? (eval-cek (prog-filter 'cons? '•)) {set '• 'nil})
(check-equal? (eval-cek (prog-filter-tc 'even? '(range 1 4))) {set '(cons 2 (cons 4 nil))})
(check-equal? (eval-cek (prog-filter-tc '• '(range 1 2)))
              {set '(blame † list) '(blame † ∆) '(blame † car) '(blame † cdr)
                   '(cons 1 (cons 2 nil)) '(cons 1 nil) '(cons 2 nil) 'nil})
(check-equal? (eval-cek (prog-filter-tc 'cons? '•)) {set '• 'nil '(blame † list)})

;; 'quick'sort
(define prog-qsort
  `(,modl-list
    (module sort
      (provide
       [sorted? (,c/real-list ↦ (flat bool?))]
       [sort (,c/real-list ↦ (and/c ,c/real-list (flat sorted?)))])
      (require list)
      (define (sort xs)
        (cond
          [(nil? xs) nil]
          [else (let* ([pivot (car xs)]
                       [rest (cdr xs)]
                       [l (filter (λ (y) (< y pivot)) rest)]
                       [r (filter (λ (y) (≥ y pivot)) rest)])
                  (append (sort l) (cons pivot (sort r))))]))
      ,defn-sorted?)
    (require list sort)
    (sort (append (range 8 10) (range 1 3)))))
(check-equal? (eval-cek prog-qsort)
              {set '(cons 1 (cons 2 (cons 3 (cons 8 (cons 9 (cons 10 nil))))))})

;; 'flatten' example from Wright paper, section 1.1
(define modl-flatten
  (let ([c/flat-list
         `(μ (flat-list?)
             (or/c (flat nil?)
                   ; TODO: add 'not' combinator for contract?
                   (cons/c (or/c (flat num?) (or/c (flat bool?) (flat string?)))
                           flat-list?)))])
    `(module flatten
       (provide
        [flatten (,c/any ↦ ,c/flat-list)]
        [a (cons/c (flat num?) (cons/c (cons/c (flat num?) (flat nil?))
                                       (cons/c (flat num?) (flat nil?))))]
        [b ,c/num-list])
       (require list)
       (define (flatten l)
         (cond
           [(nil? l) nil]
           [(cons? l) (append (flatten (car l)) (flatten (cdr l)))]
           [else (cons l nil)]))
       (define a (cons 1 (cons (cons 2 nil) (cons 3 nil))))
       (define b (flatten a)))))
(define prog-flatten-ok1 `(,modl-list
                           ,modl-flatten
                           (require flatten)
                           b))
(check-equal? (eval-cek prog-flatten-ok1) {set '(cons 1 (cons 2 (cons 3 nil)))})
(define prog-flatten-•
  `(,modl-list
    ,modl-flatten
    (require flatten)
    (flatten •)))
(check-equal? (eval-cek prog-flatten-•) {set '•})
(define prog-flatten-ok2 `(,modl-list
                           ,modl-flatten
                           (require flatten)
                           (car b)))
(check-equal? (eval-cek prog-flatten-ok2) {set 1})
(define prog-flatten-err1 `(,modl-list
                            ,modl-flatten
                            (require flatten list)
                            (map (λ (x) (+ 1 x)) a)))
(check-equal? (eval-cek prog-flatten-err1) {set '(blame † +)})
(define prog-flatten-err2
  `(,modl-list
    ,modl-flatten
    (require flatten list)
    (map (λ (x) (- x 1))
         (flatten (cons "this" (cons (cons "that" nil) nil))))))
(check-equal? (eval-cek prog-flatten-err2) {set '(blame † -)})

;; taut from Wright paper, section 5.1
(define (prog-taut p)
  (let ([c/taut `(μ (taut?) (or/c (flat bool?) ((flat bool?) ↦ taut?)))])
    `((module taut
        (provide
         [taut (,c/taut ↦ (flat bool?))])
        (define (taut b)
          (cond
            [(equal? #t b) #t]
            [(false? b) #f]
            [else (and (taut (b #t)) (taut (b #f)))])))
      (require taut)
      (taut ,p))))
(check-equal? (eval-cek (prog-taut #t)) {set #t})
(check-equal? (eval-cek (prog-taut 'not)) {set #f})
(check-equal? (eval-cek (prog-taut '(λ (x) (λ (y) (and x y))))) {set #f})
#;(check-equal? (eval-cek (prog-taut '•)) {set '(blame † taut) #t #f}) ; FIXME

;; 'member' from Wright paper Appendix
(define (prog-member x l)
  `((module member
      (provide
       [member (,c/any ,c/list ↦ ,c/list)])
      (define (member x l)
        (cond
          [(nil? l) nil]
          [(equal? x (car l)) l]
          [else (member x (cdr l))])))
    (require member)
    (member ,x ,l)))
(check-equal? (eval-cek (prog-member 3 '(cons 2 (cons 3 (cons 5 nil)))))
              {set '(cons 3 (cons 5 nil))})
(check-equal? (eval-cek (prog-member '• '(cons 2 (cons 3 (cons 5 nil)))))
              ; every possible tail
              {set '(cons 2 (cons 3 (cons 5 nil)))
                   '(cons 3 (cons 5 nil)) '(cons 5 nil) 'nil})
(check-equal? (eval-cek (prog-member '• '•)) {set '(blame † member) 'nil '•})

;; 'lastpair' from Wright paper Appendix
(define (prog-lastpair s)
  `((module lastpair
      (provide
       [lastpair ((cons/c ,c/any ,c/list) ↦ (cons/c ,c/any (flat nil?)))])
      (define (lastpair s)
        (if (cons? (cdr s)) ; TODO: this test is not remembered
            (lastpair (cdr s))
            s)))
    (require lastpair)
    (lastpair ,s)))
(check-equal? (eval-cek (prog-lastpair '(cons 1 (cons 2 nil)))) {set '(cons 2 nil)})
(check-equal? (eval-cek (prog-lastpair 'nil)) {set '(blame † lastpair)})
(check-equal? (eval-cek (prog-lastpair '•)) {set '• '(blame † lastpair)})

;; subst* from Wright paper Appendix
(define (prog-subst* new old t)
  `((module subst*
      (provide
       [subst* (,c/any ,c/any ,c/any ↦ ,c/any)])
      (define (subst* new old t)
        (cond
          [(equal? old t) new]
          [(cons? t) (cons (subst* new old (car t))
                           (subst* new old (cdr t)))]
          [else t])))
    (require subst*)
    (subst* ,new ,old ,t)))
(check-equal? (eval-cek (prog-subst* '42 '(cons 2 nil) '(cons 1 (cons (cons 2 nil) (cons 2 nil)))))
              {set '(cons 1 (cons 42 42))})
(check-equal? (eval-cek (prog-subst* '• '• '(cons 1 (cons 2 nil))))
              ; all possible substitutions, b/c (equal? old t) is not remembered
              {set '(cons • (cons 2 nil)) '(cons 1 •) '(cons 1 (cons 2 •))
                   '• '(cons 1 (cons • •)) '(cons • (cons 2 •))
                   '(cons • (cons • •)) '(cons 1 (cons 2 nil))})

;; 'Y' + 'last' from Wright paper Appendix
(define (prog-last xs)
  `((module last
      (provide
       [last ((cons/c ,c/any ,c/list) ↦ ,c/any)])
      (define last
        (Y (λ (f)
             (λ (x)
               (if (nil? (cdr x))
                   (car x)
                   (f (cdr x)))))))
      (define (Y f)
        (λ (y)
          (((λ (x) (f (λ (z) ((x x) z))))
            (λ (x) (f (λ (z) ((x x) z)))))
           y))))
    (require last)
    (last ,xs)))
(check-equal? (eval-cek (prog-last '(cons 1 (cons 2 nil)))) {set 2})
(check-equal? (eval-cek (prog-last '•)) {set '(blame † last) '•})

;; benchmarks
(define tak ; translated from http://www.larcenists.org/R6src/tak.sch
  `((module tak
      (provide
       [tak ((flat int?) (flat int?) (flat int?) ↦ (flat int?))])
      (define (tak x y z)
        (if (not (< y x))
            z
            (tak (tak (- x 1) y z)
                 (tak (- y 1) z x)
                 (tak (- z 1) x y)))))
    (require tak)
    (tak 3 2 1)))
(time (check-equal? (eval-cek tak) {set 2}) 'tak)

(define takl ; translated from http://www.larcenists.org/R6src/takl.sch
  `((module takl
      (provide
       [mas (,c/num-list ,c/num-list ,c/num-list ↦ ,c/num-list)]
       [listn ((flat nat?) ↦ ,c/num-list)])
      
      (define (listn n)
        (if (zero? n) nil (cons n (listn (- n 1)))))
      
      (define (shorter? x y)
        (and (not (nil? y))
             (or (nil? x)
                 (shorter? (cdr x) (cdr y)))))
      
      (define (mas x y z)
        (if (not (shorter? y x))
            z
            (mas (mas (cdr x) y z)
                 (mas (cdr y) z x)
                 (mas (cdr z) x y)))))
    (require takl)
    (mas (listn 3) (listn 2) (listn 1))))
(time (check-equal? (eval-cek takl) {set '(cons 2 (cons 1 nil))}) 'takl)

(define cpstak ; translated from http://www.larcenists.org/R6src/cpstak.sch
  `((module tak
      (provide
       [cpstak ((flat num?) (flat num?) (flat num?) ↦ (flat num?))])
      
      (define (cpstak x y z)
        (tak x y z (λ (a) a)))
      
      (define (tak x y z k)
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
                                 (tak v1 v2 v3 k))))))))))
    (require tak)
    (cpstak 3 2 1)))
(time (check-equal? (eval-cek cpstak) {set 2}) 'cpstak)

;; rsa example translated from
;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/rsa.scm
(define prog-rsa
  `((module rsa
      (provide
       [private-exponent
        ((flat int?) (flat int?) (flat int?) ↦ (or/c (flat int?) (flat false?)))]
       [encrypt
        ((flat int?) (flat int?) (flat int?) ↦ (or/c (flat int?) (flat false?)))]
       [decrypt ((flat int?) (flat int?) (flat int?) ↦ (flat int?))])
      
      (define (extended-gcd a b)
        (if (zero? (mod a b))
            (cons 0 1)
            (let* ([x:y (extended-gcd b (mod a b))]
                   [x (car x:y)]
                   [y (cdr x:y)])
              (cons y (- x (* y (quot a b)))))))
      
      (define (modulo-inverse a n)
        (mod (car (extended-gcd a n)) n))
      
      (define (totient p q)
        (* (- p 1) (- q 1)))
      
      (define (square x)
        (* x x))
      
      (define (modulo-power base exp n)
        (if (= exp 0) 1
            (if (odd? exp)
                (mod (* base (modulo-power base (- exp 1) n)) n)
                (mod (square (modulo-power base (/ exp 2) n)) n))))
      
      (define (legal-public-exponent? e p q)
        (and (< 1 e)
             (< e (totient p q))
             (= 1 (gcd e (totient p q)))))
      
      (define (private-exponent e p q)
        (if (legal-public-exponent? e p q)
            (modulo-inverse e (totient p q))
            #f))
      
      (define (encrypt m e n)
        (if (> m n) #f
            (modulo-power m e n)))
      
      (define (decrypt c d n)
        (modulo-power c d n)))
    
    (require rsa)
    
    (let* ([p 41] ; "large" prime
           [q 47] ; "large" prime
           [n (* p q)] ; public modulus
           [e 7] ; public exponent
           [d (private-exponent e p q)] ; private exponent
           [plaintext 42]
           [ciphertext (encrypt plaintext e n)]
           [decrypted-ciphertext (decrypt ciphertext d n)])
      (= plaintext decrypted-ciphertext))))
(time (check-equal? (eval-cek prog-rsa) {set #t}) 'rsa)

;; sat-brute translated from
;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/kcfa/sat-brute.scm
(define phi
  `(λ (x1 x2 x3 x4 x5 x6 x7)
     (and (or x1 x2)
          (or x1 (not x2) (not x3))
          (or x3 x4)
          (or (not x4) x1)
          (or (not x2) (not x3))
          (or x4 x2))))
(define (prog-sat phi)
  `((module sat
      (provide
       [sat-solve-7
        ((,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ↦ ,c/bool) ↦ ,c/bool)])
      
      (define (try f)
        (or (f #t) (f #f)))
      
      (define (sat-solve-7 p)
        (try (λ (n1)
               (try (λ (n2)
                      (try (λ (n3)
                             (try (λ (n4)
                                    (try (λ (n5)
                                           (try (λ (n6)
                                                  (try (λ (n7)
                                                         (p n1 n2 n3 n4 n5 n6 n7)))))))))))))))))
    (module phi
      (provide
       [phi (,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ↦ ,c/bool)])
      (define phi ,phi))
    (require sat phi)
    (sat-solve-7 phi)))
(time (check-equal? (eval-cek (prog-sat phi)) {set #t}) 'sat-7)
(time (check-equal? (eval-cek (prog-sat '•))
                    ; FIXME
                    {set #t #f '(blame † sat) '(blame phi ∆) '(blame phi car) '(blame phi cdr)})
      'sat-7-•)

;; 'worst case', translated from
;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/kcfa-worst-case.scm
(define prog-worst-case
  `(((λ (f1)
       (let ([a (f1 #t)])
         (f1 #f)))
     (λ (x1) ((λ (f2)
                (let ([b (f2 #t)])
                  (let ([c (f2 #f)])
                    (f2 #t))))
              (λ (x2) ((λ (z) (z x1 x2)) (λ (y1 y2) y1))))))))
(time (check-equal? (eval-cek prog-worst-case) {set #f}) 'worst-case)

;; 'even worse', translated from
;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/kcfa-even-worse.scm
(define prog-even-worse
  `(((λ (f1)
       (let ([a (f1 #t)])
         (f1 #f)))
     (λ (x1)
       ((λ (f2)
          (let ([b (f2 #t)])
            (f2 #f)))
        (λ (x2)
          ((λ (f3)
             (let ([c (f3 #t)])
               (f3 #f))) (λ (x3) ((λ (z) (z x1 x2 x3)) (λ (y1 y2 y3) y1))))))))))
(time (check-equal? (eval-cek prog-even-worse) {set #f}) 'even-worse)

;; mutual tail calls from different modules
;; make sure stack doesn't grow
(define prog-even?
  `((module ev
      (provide [ev? ((flat nat?) ↦ (flat bool?))])
      (require od)
      (define (ev? n)
        (or (zero? n) (od? (- n 1)))))
    (module od
      (provide [od? ((flat nat?) ↦ (flat bool?))])
      (require ev)
      (define (od? n)
        (and (not (zero? n)) (ev? (- n 1)))))
    (module n
      (provide [n (flat nat?)])
      (define n •))
    (require ev n)
    (ev? n)))
; TODO: system also thinks (blame ev od) and (blame od ev) b/c
;; it doesn't know that (NonzeroNat - 1) is also a Nat
(check-equal? (eval-cek prog-even?) {set #t #f})

;; test var-args function
(define (prog-max . args)
  `(,modl-list
    (module max
      (provide
       [max ((flat real?) (flat real?) .. ↦ (flat real?))])
      (require list)
      
      (define (max x xs ..)
        (cond
          [(nil? xs) x]
          [else (foldl max2 x xs)]))
      
      (define (max2 x y)
        (if (> x y) x y)))
    (require max)
    (max ,@ args)))
(check-equal? (eval-cek (prog-max 4 3 5 2 6)) {set 6})
(check-equal? (eval-cek (prog-max)) {set '(blame † max)})
(check-equal? (eval-cek (prog-max 4 3 5 '•)) {set 5 '• '(blame † max)})

;; applying var-args contract on fixed-args function
;; errors won't be detected unless function is applied on wrong number of args
;; is this behavior preferred? It turned out i did less work for this
(define (prog-max-wrong . args)
  `((module max
      (provide
       [max ((flat real?) (flat real?) .. ↦ (flat real?))])
      (define (max x y)
        (if (> x y) x y)))
    (require max)
    (max ,@ args)))
(check-equal? (eval-cek (prog-max-wrong 1 2)) {set 2}) ; max is lucky
(check-equal? (eval-cek (prog-max-wrong 1 2 3))
              ; max doesn't deliver what it promises
              {set '(blame max max)})

;; test read/show
#;(for-each
   (λ (p)
     (check-equal?
      (read-prog p)
      ((compose read-prog show-prog read-prog) p)))
   (list prog-db00 prog-db01 prog-db10 prog-db00-2
         (prog-factorial modl-factorial '•) prog-rsa prog-ins-sort prog-qsort
         prog-even-list-ok prog-even-list-err
         prog-func-pair-ok prog-func-pair-err1 prog-func-pair-err2
         prog-flatten-ok1 prog-flatten-ok2 prog-flatten-err1 prog-flatten-err2
         (prog-taut '•)
         tak takl cpstak))

;; for debugging
(define step1 (curry non-det step))
(define (pow f n) (apply compose (make-list n f)))
(define (step* k e) ((pow step1 k) (set (load (read-exp e)))))
