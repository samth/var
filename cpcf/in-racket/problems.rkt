#lang racket

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

(require rackunit)

;; local helper function without contract
'(sum-acc does not have a contract - result approximated with •)
(eval-cek
 `((module sum
     (provide
      [sum (,c/num-list ↦ (flat num?))]
      [xs ,c/num-list])
     (define (sum xs)
       (sum-acc xs 0))
     
     (define (sum-acc xs acc)
       (cond
         [(nil? xs) acc]
         [else (sum-acc (cdr xs) (+ (car xs) acc))]))
     
     (define xs •))
   (require sum)
   (sum xs)))

;; functions defined through foldr and foldl lose precision because
;; foldr and foldl have generic, imprecise contracts
(define modl-list
  `(module list
     (provide
      [foldl ((,c/any ,c/any ↦ ,c/any) ,c/any ,c/list ↦ ,c/any)]
      [foldr ((,c/any ,c/any ↦ ,c/any) ,c/any ,c/list ↦ ,c/any)]
      [nums ,c/num-list])
     
     (define (foldl f z xs)
       (cond
         [(nil? xs) z]
         [else (foldl f (f (car xs) z) (cdr xs))]))
     
     (define (foldr f z xs)
       (cond
         [(nil? xs) z]
         [else (f (car xs) (foldr f z (cdr xs)))]))
     (define nums •)))

'(result of foldr is approximated with •)
(eval-cek
 `(,modl-list
   (module sum
     (provide
      [sum (,c/num-list ↦ (flat num?))])
     (require list)
     (define (sum xs)
       (foldr + 0 xs)))
   (require list sum)
   (sum nums)))

'(result of foldl is approximated with •)
(eval-cek
 `(,modl-list
   (module sum
     (provide
      [sum (,c/num-list ↦ (flat num?))])
     (require list)
     (define (sum xs)
       (foldl + 0 xs)))
   (require list sum)
   (sum nums)))

'(direct definition of sum works fine)
(eval-cek
 `(,modl-list
   (module sum
     (provide
      [sum (,c/num-list ↦ (flat num?))])
     (define (sum xs)
       (cond
         [(nil? xs) 0]
         [else (+ (car xs) (sum (cdr xs)))])))
   (require sum list)
   (sum nums)))

;; insensitivity to control flow
(eval-cek
 `((module m1
     (provide
      ; system is falsely blamed for misuse of car and cdr when expanding cons/c
      [f ((cons/c ,c/any ,c/any) ↦ ,c/any)]
      [g (,c/any ↦ ,c/any)])
     (define f car)
     (define (g x)
       (cond ; m1 is also blamed for using car here
         [(cons? x) (car x)]
         [else x])))
   (module m2
     (provide
      [x ,c/any])
     (define x •))
   (require m1 m2)
   (g x)))

;; last-pair program from Wright paper
(eval-cek
 `((module lastpair
     (provide
      [lastpair ((cons/c ,c/any ,c/list) ↦ (cons/c ,c/any (flat nil?)))])
     (define (lastpair s)
       (if (cons? (cdr s))
           (lastpair (cdr s)) ; it's not remembered that (cdr s) is a pair
           s)))
   (module x
     (provide
      [x (cons/c ,c/any ,(c/list-of c/any))])
     (define x •))
   (require lastpair x)
   (lastpair x)))