#lang racket

(require (prefix-in r: racket))

(define ((sorted/c c) l)
  (if (null? l) #t      
      (let loop ([last (car l)]
                 [l (cdr l)])
        (if (null? l) 
            #t
            (and (memq (c last (car l)) '(lt eq))
                 (loop (car l) (cdr l)))))))

(define/contract (sort cmp l)
  (->i ([c (integer? integer? . -> . (one-of/c 'lt 'gt 'eq))] [l (listof integer?)])
       [_ (c) (and/c (listof integer?)
                     (sorted/c c))])
  (r:sort l (λ (x y) (eq? 'lt (cmp x y)))))

(define (lt x y)
  (cond [(< x y) 'lt]
        [(> x y) 'gt]
        [else 'eq]))

(define (gt x y)
  (cond [(< x y) 'gt]
        [(> x y) 'lt]
        [else 'eq]))

(sort lt '(3 2 1))

(sort gt '(3 2 1))

(sort gt '(3 2 1 5))