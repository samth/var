#lang var  ;count ;trace

(define-contract list/c
  (rec/c X (or/c empty? (cons/c nat? X))))

(module sorted-ne? racket
  ; ...
  (provide/contract [sorted-ne? (list/c -> bool?)]))

(module sorted? racket 
  (require (only-in sorted-ne? sorted-ne?))
  (define (sorted? l) (if (empty? l) #t (sorted-ne? l)))
  (provide/contract [sorted? (list/c -> bool?)]))

(module insert racket 
  (require (only-in sorted? sorted?))
  ; ...
  (provide/contract [insert (nat? (and/c list/c sorted?) -> (and/c list/c sorted?))]))

(module insertion-sort racket  
  (require (only-in insert insert) (only-in sorted? sorted?))
  (define (insertion-sort l acc) (if (empty? l) acc (insertion-sort (rest l) (insert (first l) acc))))
  (provide/contract [insertion-sort (list/c (and/c list/c sorted?) -> (and/c list/c sorted?))]))

(module n racket 
  ; ...
  (provide/contract [n list/c]))

(require (only-in n n) (only-in insertion-sort insertion-sort))
(insertion-sort n empty)

