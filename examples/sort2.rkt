#lang s-exp "../verified.rkt"

(define-contract list/c
  (rec/c X (or/c empty? (cons/c nat? X))))

(module sorted-ne? (any? -> bool?) •)
(module sorted? (list/c -> bool?) 
  (λ (l) 
    (if (empty? l) 
        #t 
        (sorted-ne? l))))

(module insert (nat? (and/c list/c sorted?)
                  -> (and/c list/c sorted?))
  •)

(module insertion-sort
  (list/c (and/c list/c sorted?) -> (and/c list/c sorted?))
  (λ (l acc)
    (if (empty? l) 
        acc
        (insertion-sort (rest l)
                        (insert (first l) acc)))))


(module sort.0
  (list/c -> (and/c list/c sorted?))
  (λ (l)
    (insertion-sort l empty)))

(module foldl 
  any?
  (λ (f b ls)
    (if (empty? ls) 
        b
        (foldl f (f (first ls) b) (rest ls)))))

(module foldr
  any?
  (λ (f b ls)
    (if (empty? ls)
        b
        (f (first ls) (foldr f b (rest ls))))))

(module sort.1
  (list/c -> (and/c list/c sorted?))
  (λ (l)
    (foldl insert empty l)))

(module l list/c •)
;(insertion-sort l empty)
(sort.0 l)

;(fl insert empty l)
;(sort l)
;(fl (λ (x y) (cons x y)) empty (cons 1 (cons 2 empty)))
