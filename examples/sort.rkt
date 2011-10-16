#lang var  ;count ;trace

(define-contract list/c
  (rec/c X (or/c empty? (cons/c exact-nonnegative-integer? X))))

(module sorted-ne? racket
  ; ...
  (provide/contract [sorted-ne? (-> list/c boolean?)]))

(module sorted? racket 
  (require (only-in sorted-ne? sorted-ne?))
  (define (sorted? l) (if (empty? l) #t (sorted-ne? l)))
  (provide/contract [sorted? (-> list/c boolean?)]))

(module insert racket 
  (require (only-in sorted? sorted?))
  ; ...
  (provide/contract [insert (-> exact-nonnegative-integer? (and/c list/c sorted?) (and/c list/c sorted?))]))

(module insertion-sort racket 
  ; BUG: doesn't work if written like this: 
  ; (require 'insert 'sorted?)
  (require (only-in insert insert) (only-in sorted? sorted?))
  (define (insertion-sort l acc) (if (empty? l) acc (insertion-sort (rest l) (insert (first l) acc))))
  (provide/contract [insertion-sort (-> list/c (and/c list/c sorted?) (and/c list/c sorted?))]))

(module n racket 
  ; ...
  (provide/contract [n list/c]))

(require 'n 'insertion-sort)
(insertion-sort n empty)

