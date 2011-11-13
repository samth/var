#lang var rho eval ;count ;trace
(module sorted-ne? racket
  ; ...
  (provide/contract [sorted-ne? (-> (listof exact-nonnegative-integer?) boolean?)]))

(module sorted? racket 
  (require (only-in sorted-ne? sorted-ne?))
  (define (sorted? l) (if (empty? l) #t (sorted-ne? l)))
  (provide/contract [sorted? (-> (listof exact-nonnegative-integer?) boolean?)]))

(module insert racket 
  (require (only-in sorted? sorted?))
  ; ...
  (provide/contract [insert (-> exact-nonnegative-integer? (and/c (listof exact-nonnegative-integer?) sorted?) (and/c (listof exact-nonnegative-integer?) sorted?))]))

(module insertion-sort racket 
  ; BUG: doesn't work if written like this: 
  ; (require 'insert 'sorted?)
  (require (only-in insert insert) (only-in sorted? sorted?))
  (define (insertion-sort l acc) (if (empty? l) acc (insertion-sort (cdr l) (insert (car l) acc))))
  (provide/contract [insertion-sort ((listof exact-nonnegative-integer?) 
                                     (and/c (listof exact-nonnegative-integer?) sorted?)
                                     . -> .
                                     (and/c (listof exact-nonnegative-integer?) sorted?))]))

(module n racket 
  ; ...
  (provide/contract [n (listof exact-nonnegative-integer?)]))

(require 'n 'insertion-sort)
(insertion-sort n empty)

