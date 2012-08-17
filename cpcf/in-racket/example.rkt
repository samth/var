#lang racket
((module num
   (provide
    [even? ((flat nat?) ↦ (flat bool?))]
    [odd? ((flat nat?) ↦ (flat bool?))]
    [max ((flat num?) (flat num?) .. ↦ (flat num?))])
   (require list)
   
   (define (even? n)
     (or (zero? n)
         (odd? (- n 1))))
   
   (define (odd? n)
     (and (not (zero? n))
          (even? (- n 1))))
   
   (define (max2 x y)
     (if (> x y) x y))
   
   (define (max x xs ..)
     (cond
       [(nil? xs) x]
       [else (foldl max2 x xs)])))
 
 (module list
   (provide
    [foldr ((,c/any ,c/any ↦ ,c/any) ,c/any ,c/list ↦ ,c/any)]
    [foldl ((,c/any ,c/any ↦ ,c/any) ,c/any ,c/list ↦ ,c/any)]
    [filter ((,c/any ↦ ,c/any) ,c/list ↦ (λ (p xs)
                                           (μ (all-p?)
                                              (or/c (flat nil?)
                                                    (cons/c (flat p) all-p?)))))]
    [filter-tc ((,c/any ↦ ,c/any) ,c/list ↦ (λ (p xs)
                                              (μ (all-p?)
                                                 (or/c (flat nil?)
                                                       (cons/c (flat p) all-p?)))))]
    [map ((,c/any ↦ ,c/any) ,c/list ↦ ,c/list)]
    [map-tc ((,c/any ↦ ,c/any) ,c/list ↦ ,c/list)]
    [reverse (,c/list ↦ ,c/list)]
    [append (,c/list ,c/list ↦ ,c/list)])
   
   (define (foldr op a xs)
     (cond
       [(nil? xs) a]
       [else (op (car xs) (foldr op a (cdr xs)))]))
   
   (define (foldl op a xs)
     (cond
       [(nil? xs) a]
       [else (foldl op (op a (car xs)) (cdr xs))]))
   
   (define (map f xs)
     (foldr (λ (x ys) (cons (f x) ys)) nil xs))
   
   (define (map-fc f xs)
     (reverse (foldl (λ (x ys) (cons (f x) ys)) nil xs)))
   
   (define (filter p xs)
     (foldr (λ (x ys) (if (p x) (cons x ys) ys)) nil xs))
   
   (define (filter-tc p xs)
     (reverse (foldl (λ (x ys) (if (p x) (cons x ys) ys)) nil xs)))
   
   (define (reverse xs)
     (foldl cons nil xs))
   
   (define (append xs ys)
     (foldr cons ys xs)))
 
 (max 1 2 3 4 5))