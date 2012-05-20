#lang racket

(require "scpcf-lang.rkt")

(provide
 ;; ExpSet := [Listof Exp]
 
 ;; Verified := 'Proved | 'Refuted | 'Neither
 
 ;; eval1, eval* : Exp -> ExpSet
 eval1 eval*
 
 ;; interact1, interact* : -> [Listof S-exp]
 ;; reads in expression in SCPCF, returns possible results in S-exp
 interact1 interact*)

;; interact1, interact* : -> [Listof S-exp]
(define (interact1) (interact-with eval1))
(define (interact*) (interact-with eval*))

;; interact-with : (Exp -> ExpSet) -> [Listof S-exp]
(define (interact-with func)
  (let ([e (read-exp (read))])
    (match (type-check e)
      ['TypeError (error "Does not type check")]
      [else (map show-exp (func e))])))

;; eval* : Exp -> (ExpSet, with all members being answers)
(define (eval* e)
  (fix (non-det eval1) (singleton e) exp-set=?))

;; eval1 : Exp -> ExpSet
;; actually, eval1's reflexive closure
(define (eval1 e)
  (match e
    [(value u cs) {singleton e}]
    [(blame l1 l2) {singleton e}]
    [(app e1 e2) ; TODO apply •
     (match `(,e1 ,e2)
       [`(,(value (lam x t body) cs1) ,(value u cs2))
        {singleton (subst x e2 body)}]
       [`(,(value (lam x t body) cs1) _)
        {(non-det (curry app e1)) (eval1 e2)}]
       [else {(non-det (λ (func) (app func e2))) (eval1 e1)}])]
    [(rec f t e) (subst f (rec f t e) e)]
    [(if/ e1 e2 e3)
     (match e1
       [(value u cs)
        {(non-det (λ (b) {singleton
                          (match b
                            [(value #t _) e2]
                            [(value #f _) e3])}))
         (δ 'true? `(,e1))}]
       [else {(non-det (λ (test) {singleton (if/ test e2 e3)}))
              (eval1 e1)}])]
    [(prim-app o args)
     (if (andmap value? args) {δ o args}
         (let ([z (split-at (compose not value?) args)])
           {(non-det
             (λ (v)
               {singleton (prim-app o (combine (replace v z)))}))
            (eval1 (focus z))}))]
    [(mon h f g c e)
     (match e
       [(value u cs)
        {singleton
         (match c
           [(flat/c p)
            (match (verify c (value u cs))
              ['Proved (value u cs)]
              ['Refuted (blame f h)]
              ['Neither (if/ (app p e) (refine e c) (blame f h))])]
           [(func/c C x t D)
            (lam x t (mon h f g D (app e (mon h g f C x))))])}]
       [else {(non-det (λ (v) (mon h f g c v))) (eval1 e)}])]
    ; type-checked programs can't reach here
    [else (error "eval1: unexpected: " e)]))

;; non-det : (Exp -> ExpSet) -> (ExpSet -> ExpSet)
;; like >>=, but remove duplicates, specialized for exps
(define (non-det f)
  (λ (exps) (foldr ∪ empty (map f exps))))

;; ExpSet = ListOf Exp (for now)

;; ∪ : ExpSet ExpSet -> ExpSet
(define (∪ s1 s2)
  ;; cons-exp : Exp ExpSet -> ExpSet
  (define (cons-exp e es)
    (if (ormap (curry exp=? e) es) es (cons e es)))
  (foldr cons-exp s2 s1))

;; exp-set=? : ExpSet ExpSet -> ExpSet
(define (exp-set=? s1 s2)
  (and (= (length s1) (length s2))
       (⊂ s1 s2)))

;; ⊂ : ExpSet ExpSet -> Boolean
(define (⊂ s1 s2)
  (andmap (λ (x) (member x s2)) s1))

;; singleton : Exp -> ExpSet
(define (singleton x) (list x))

;; verify : Value Contract -> Verified
(define (verify v c)
  (if (ormap (curry con=? c) (value-refinements v))
      'Verified
      'Neither))

;; fix : (x -> x) x (x x -> Boolean) -> x
(define (fix f x =?)
  ;; go : x x -> x
  (define (go x y)
    (if (=? x y) x (go y (f y))))
  (go x (f x)))

;; refine : Value Contract -> Value
;; assumes value does not already prove contract at this point
(define (refine v c)
  (value (value-pre v) (cons c (value-refinements v))))

;; Zipper x = (list [Listof x] x [Listof x])
;; [1,2,3,4,5] focused at 3: (list [2,1] [3,4,5])

;; split : [x -> Boolean] [Listof x] -> [Zipper x]
(define (split-at p xs)
  ;; go : [Listof x] [Listof x] -> [Zipper x]
  (define (go l r)
    (match r
      [(cons x xs) (if (p x) (list l r) (go (cons x l) xs))]
      [empty (list l r)]))
  (go empty xs))

;; replace : [x -> x] [Zipper x] -> [Zipper x]
(define (replace x1 z)
  (match z
    [(list l (cons r rs)) (list l (cons x1 rs))]
    [else z]))

;; combine : [Zipper x] -> [Listof x]
(define (combine z)
  (foldl cons (second z) (first z)))

;; focus : [Zipper x] -> x
(define (focus z)
  (first (second z)))


