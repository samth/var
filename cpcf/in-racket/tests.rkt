#lang racket
(require rackunit)

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

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
(define modl-factorial
  `(module fac ((flat int?) ↦ (flat int?))
     (μ (fac) (λ (n) (if (zero? n) 1 (* n (fac (- n 1))))))))
(define modl-factorial-acc
  `(module fac ((flat num? #|TODO|#) ↦ (flat num? #|TODO|#))
     (let ([fac1 (μ (go)
                    (λ (n acc)
                      (if (zero? n) acc
                          (go (- n 1) (* n acc)))))])
       (λ (n) (fac1 n 1)))))
(define (prog-factorial mod-fac n)
  `(,mod-fac
    (fac ,n)))
(check-equal? (eval-cek (prog-factorial modl-factorial 3)) {set 6})
#;(check-equal? (eval-cek (prog-factorial modl-factorial '•))
                {set '• '(blame † fac)}) ; won't terminate
(check-equal? (eval-cek (prog-factorial modl-factorial-acc 3)) {set 6})
(check-equal? (eval-cek (prog-factorial modl-factorial-acc '•))
              {set '• '(blame † fac)})

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
              (foldl f (f (car xs) a) (cdr xs)))))))
(define modl-reverse
  `(module reverse (,c/list ↦ ,c/list)
     (λ (xs)
       (foldl cons nil xs))))
(define modl-map
  `(module map ((,c/any ↦ ,c/any) ,c/list ↦ ,c/list)
     (λ (f xs)
       (foldr (λ (x ys) (cons (f x) ys)) nil xs))))
(define modl-filter
  `(module filter ((,c/any ↦ ,c/any) ,c/list ↦ ,c/list)
     (λ (p xs)
       (foldr (λ (x ys) (if (p x) (cons x ys) ys)) nil xs))))
(define modl-filter-tc
  `(module filter ((,c/any ↦ ,c/any) ,c/list ↦ ,c/list)
     (λ (p xs)
       (let ([loop (μ (go)
                      (λ (xs acc)
                        (if (nil? xs)
                            (reverse acc)
                            (let ([x (car xs)])
                              (go (cdr xs) (if (p x) (cons x acc) acc))))))])
         (loop xs nil)))))
(define modl-append
  `(module append (,c/list ,c/list ↦ ,c/list)
     (λ (xs ys)
       (foldr cons ys xs))))
(define modl-range
  `(module range ((flat num?) (flat num?) ↦ ,c/real-list)
     (μ (range)
        (λ (lo hi)
          (if (≤ lo hi)
              (cons lo (range (+ 1 lo) hi))
              nil)))))
#;(define modl-sorted?
  `(module sorted? (,c/real-list ↦ (flat bool?))
     (μ (sorted?)
        (λ (xs)
          (or (nil? xs)
              (nil? (cdr xs))
              (and (≤ (car xs) (car (cdr xs)))
                   (sorted? (cdr xs))))))))
(define modl-sorted?
  `(module sorted? (,c/real-list ↦ (flat bool?))
     (μ (sorted?)
        (λ (xs)
          (if (cons? xs)
              (let ([zs (cdr xs)])
                (if (cons? zs)
                    (and (≤ (car xs) (car zs))
                         (sorted? (cdr xs)))
                    #t))
              #t)))))

;; insertion sort example from section 1
(define prog-ins-sort
  `(,modl-sorted?
    (module insert ((flat num?) (and/c ,c/real-list (flat sorted?)) ↦ (and/c ,c/real-list (flat sorted?))) •)
    (module nums ,c/real-list •)
    ,modl-foldl
    (module sort (,c/real-list ↦ (and/c ,c/real-list (flat sorted?)))
      (λ (l)
        (foldl insert nil l)))
    (sort nums)))
(check-equal? (eval-cek prog-ins-sort) {set '• 'nil})

;; 'length' from section 4.4
(define modl-length
  `(module len (,c/list ↦ (flat int?))
     (μ (len)
        (λ (l)
          (if (nil? l) 0
              (+ 1 (len (cdr l))))))))
(define modl-length-acc
  `(module len (,c/list ↦ (flat int?))
     (let ([len-acc (μ (go)
                       (λ (l acc)
                         (if (nil? l) acc
                             (go (cdr l) (+ 1 acc)))))])
       (λ (l) (len-acc l 0)))))
(define (prog-length mod-len l)
  `(,mod-len (len ,l)))
(check-equal? (eval-cek (prog-length modl-length '(cons 1 (cons 2 nil)))) {set 2})
#;(check-equal? (eval-cek (prog-length modl-length '•)) {set '(blame '† 'len) '•}) ; won't terminate
(check-equal? (eval-cek (prog-length modl-length-acc '(cons 1 (cons 2 nil)))) {set 2})
#;(check-equal? (eval-cek (prog-length modl-length-acc '•)) {set '(blame '† 'len) '•}) ; won't terminate

;; 'filter'
(define (prog-filter filter-mod p xs)
  `(,modl-foldr
    ,modl-foldl
    ,filter-mod
    ,modl-range
    ,modl-reverse
    (filter ,p ,xs)))
(check-equal? (eval-cek (prog-filter modl-filter 'even? '(range 1 4)))
              {set '(cons 2 (cons 4 nil))})
(check-equal? (eval-cek (prog-filter modl-filter '• '(range 1 2))) ; every possible subsequence
              {set '(blame † filter) '(blame † ∆) '(blame † car) '(blame † cdr)
                   '(cons 1 (cons 2 nil)) '(cons 1 nil) '(cons 2 nil) 'nil})
#;(check-equal? (eval-cek (prog-filter modl-filter  'cons? '•)) {set '• 'nil}) ; won't terminate
(check-equal? (eval-cek (prog-filter modl-filter-tc 'even? '(range 1 4)))
              {set '(cons 2 (cons 4 nil))})
(check-equal? (eval-cek (prog-filter modl-filter-tc '• '(range 1 2)))
              {set '(blame † filter) '(blame † ∆) '(blame † car) '(blame † cdr)
                   '(cons 1 (cons 2 nil)) '(cons 1 nil) '(cons 2 nil) 'nil})
(check-equal? (eval-cek (prog-filter modl-filter-tc 'cons? '•))
              {set '• 'nil '(blame † filter)})

;; 'quick'sort
(define prog-qsort
  `(,modl-foldr
    ,modl-range
    ,modl-append
    ,modl-filter
    ,modl-sorted?
    (module sort (,c/real-list ↦ (and/c ,c/real-list (flat sorted?)))
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
(define prog-flatten-•
  `(,modl-foldr
    ,modl-flatten
    ,modl-append
    (flatten •)))
#;(check-equal? (eval-cek prog-flatten-•) {set '•}) ; won't terminate
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
  (let ([T? `(λ (x) (equal? #t x))]
        [F? 'false?]
        [c/taut `(μ (taut?) (or/c (flat bool?) ((flat bool?) ↦ taut?)))])
    `((module taut (,c/taut ↦ (flat bool?))
        (μ (taut)
           (λ (b)
             (if (,T? b) #t
                 (if (,F? b) #f
                     (and (taut (b #t)) (taut (b #f))))))))
      (taut ,p))))
(check-equal? (eval-cek (prog-taut #t)) {set #t})
(check-equal? (eval-cek (prog-taut 'not)) {set #f})
(check-equal? (eval-cek (prog-taut '(λ (x) (λ (y) (and x y))))) {set #f})
#;(check-equal? (eval-cek (prog-taut '•)) {set '(blame † taut) #t #f}) ; FIXME

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
(check-equal? (eval-cek (prog-member '• '•)) {set '(blame † member) 'nil '•})

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
(check-equal? (eval-cek (prog-lastpair '•)) {set '• '(blame † lastpair)})

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
(check-equal? (eval-cek (prog-subst* '• '• '(cons 1 (cons 2 nil))))
              ; all possible substitutions, b/c (equal? old t) is not remembered
              {set '(cons • (cons 2 nil)) '(cons 1 •) '(cons 1 (cons 2 •))
                   '• '(cons 1 (cons • •)) '(cons • (cons 2 •))
                   '(cons • (cons • •)) '(cons 1 (cons 2 nil))})

;; 'Y' + 'last' from Wright paper Appendix
(define (prog-last xs)
  `((module Y ,c/any #|TODO|#
      (λ (f)
        (λ (y)
          (((λ (x) (f (λ (z) ((x x) z))))
            (λ (x) (f (λ (z) ((x x) z)))))
           y))))
    (module last ((cons/c ,c/any ,c/list) ↦ ,c/any)
      (Y (λ (f)
           (λ (x)
             (if (nil? (cdr x))
                 (car x)
                 (f (cdr x)))))))
    (last ,xs)))
(check-equal? (eval-cek (prog-last '(cons 1 (cons 2 nil)))) {set 2})
(check-equal? (eval-cek (prog-last '•)) {set '(blame † last) '•})

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
(time (check-equal? (eval-cek tak) {set 2}) 'tak)

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
(time (check-equal? (eval-cek takl) {set '(cons 2 (cons 1 nil))}) 'takl)

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
(time (check-equal? (eval-cek cpstak) {set 2}) 'cpstak)

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
(time (check-equal? (eval-cek prog-rsa) {set #t}) 'rsa)

;; sat-brute translated from
;; https://github.com/ilyasergey/reachability/blob/master/benchmarks/kcfa/sat-brute.scm
(define modl-phi
  `(module phi (,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ↦ ,c/bool)
     (λ (x1 x2 x3 x4 x5 x6 x7)
       (and (or x1 x2)
            (or x1 (not x2) (not x3))
            (or x3 x4)
            (or (not x4) x1)
            (or (not x2) (not x3))
            (or x4 x2)))))
(define modl-phi-•
  `(module phi (,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ↦ ,c/bool) •))

(define (prog-sat phi-mod)
  `(,phi-mod
    
    (module try ((,c/bool ↦ ,c/bool) ↦ ,c/bool)
      (λ (f)
        (or (f #t) (f #f))))
    
    (module sat-solve-7
      ((,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ,c/bool ↦ ,c/bool)
       ↦ ,c/bool)
      (λ (p)
        (try (λ (n1)
               (try (λ (n2)
                      (try (λ (n3)
                             (try (λ (n4)
                                    (try (λ (n5)
                                           (try (λ (n6)
                                                  (try (λ (n7)
                                                         (p n1 n2 n3 n4 n5 n6 n7)))))))))))))))))
    
    
    (sat-solve-7 phi)))
(time (check-equal? (eval-cek (prog-sat modl-phi)) {set #t}) 'sat-7)
(time (check-equal? (eval-cek (prog-sat modl-phi-•))
                    ; FIXME
                    {set #t #f '(blame phi ∆) '(blame phi car) '(blame phi cdr)})
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


;; test read/show
(for-each
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
