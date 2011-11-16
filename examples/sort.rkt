#lang var rho eval

(module ne-sorted? racket
  (provide/contract [ne-sorted? (-> (listof exact-nonnegative-integer?) boolean?)]))

(module sorted? racket
  (require 'ne-sorted?)
  (define (sorted? x)
    (if (empty? x) #t
        (ne-sorted? x)))
  (provide/contract [sorted? (-> (listof exact-nonnegative-integer?) boolean?)]))

(module insert racket 
  (require 'sorted?)
  ; ...
  (provide/contract [insert (-> exact-nonnegative-integer? (and/c (listof exact-nonnegative-integer?) sorted?) (and/c (listof exact-nonnegative-integer?) sorted?))]))

(module insertion-sort racket 
  (require 'insert 'sorted?)
  (define (insertion-sort l acc) (if (empty? l) acc (insertion-sort (cdr l) (insert (car l) acc))))
  (provide/contract [insertion-sort (-> (listof exact-nonnegative-integer?) (and/c (listof exact-nonnegative-integer?) sorted?) (and/c (listof exact-nonnegative-integer?) sorted?))]))

(module n racket 
  ; ...
  (provide/contract [n (listof exact-nonnegative-integer?)]))

(require 'n 'insertion-sort)
(insertion-sort n empty)

