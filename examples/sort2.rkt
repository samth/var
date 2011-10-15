#lang s-exp "../verified.rkt"

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

(module fold racket
  (require)
  (define foldl 
    (λ (f b ls)
      (if (empty? ls) 
          b
          (foldl f (f (first ls) b) (rest ls)))))
  (define foldr
    (λ (f b ls)
      (if (empty? ls)
          b
          (f (first ls) (foldr f b (rest ls))))))
  (provide/contract [foldl any?] [foldr any?]))

(module sort racket
  (require (only-in insertion-sort insertion-sort) (only-in insert insert) (only-in sorted? sorted?))
  (define sort.0 (λ (l) (insertion-sort l empty)))
  (define sort.1 (λ (l) (foldl insert empty l)))
  (provide/contract [sort.0 (list/c -> (and/c list/c sorted?))]
                    [sort.1 (list/c -> (and/c list/c sorted?))]))

(define/contract l list/c •)
(require (only-in sort sort.0 sort.1) (only-in l l))
;(insertion-sort l empty)
(sort.0 l)

;(fl insert empty l)
;(sort l)
;(fl (λ (x y) (cons x y)) empty (cons 1 (cons 2 empty)))
