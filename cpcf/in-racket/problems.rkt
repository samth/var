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