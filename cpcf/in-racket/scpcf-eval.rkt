#lang racket

(require rackunit)
(require "scpcf-lang.rkt")
(require racket/contract)

(provide
 (contract-out
  ;[eval1 (exp? . -> . exp-set?)]
  [eval (exp? . -> . (set/c answer?))]
  
  ;; reads in s-exp, evals, prints out result
  ;[interact1 (-> (listof s-exp?))]
  [interact* (-> (listof s-exp?))]))

;; interact1, interact* : -> [Listof S-exp]
#;(define (interact1) (interact-with eval1))
(define (interact*) (interact-with eval*))

;; interact-with : (Exp -> ExpSet) -> [Listof S-exp]
(define (interact-with func)
  (let ([e (read-exp (read))])
    (match (type-check e)
      ['TypeError (error "Does not type check")]
      [else (map show-exp (set->list (func e)))])))

(struct cek (exp env kont))

;; load : Exp -> CEK
;; returns initial machine state for closed expression

;; eval* : Exp -> (ExpSet, with all members being answers)
(define (eval* e)
  
  ;; non-det : (Exp -> ExpSet) -> (ExpSet -> ExpSet)
  ;; like >>= flipped, but remove duplicates, specialized for exps
  (define (non-det f)
    (λ (exps) (foldr ∪ empty (map f exps))))
  
  (fix (non-det eval1) (single e) exp-set=?))

;; eval1 : Exp -> ExpSet
;; actually, eval1's reflexive closure
(define (eval1 e)
  
  ;; with-range-subst : Value FunContract -> Contract
  ;; given function contract, return its range with value substituted
  (define (with-range-subst v c)
    (match c
      [(func/c c x t d) (subst-con x v d)]))
  
  ;; havoc : (FuncType | BaseType) -> Exp
  (define (havoc t)
    (match t
      [(func-type tx ty)
       (lam 'x t (app (havoc ty) (app 'x (value (opaque tx)))))]
      [else (rec 'x 'Int 'x)]))
  
  ;; exp-set-map : (Exp -> Exp) ExpSet -> ExpSet
  ;; like map, but remove duplicates, not guaranteed to preserve 'shape'
  (define (exp-set-map f es)
    (foldr (λ (e es1) (cons-exp (f e) es1)) empty es))
  
  ;; eval1-app : Exp Exp -> ExpSet
  (define (eval1-app e1 e2)
    (match `(,e1 ,e2)
      [`(,(value (lam x t body) cs1) ,(value u cs2)) ;; ((λ ..) V)
       {single (subst x e2 body)}]
      [`(,(value (opaque (func-type t1 t2)) cs1) ,(value u cs2)) ;; (• V)
       `{,(value (opaque t2) (map (curry with-range-subst e2) cs1))
         ,(app (havoc t1) e2)}]
      [`(,(value u cs1) ,arg) ;; (V E)
       {exp-set-map (λ (arg) (app e1 arg)) (eval1 arg)}]
      [else {exp-set-map (λ (func) (app func e2)) (eval1 e1)}])) ;; (E E)
  
  ;; eval1-if : Exp Exp Exp -> ExpSet
  (define (eval1-if e1 e2 e3)
    (match e1
      [(value u cs)
       {exp-set-map (λ (b) (if (value-pre b) e2 e3))
                    (δ 'true? `(,e1))}]
      [else {exp-set-map (λ (test) (if/ test e2 e3))
                         (eval1 e1)}]))
  
  ;; eval1-prim : Op [Listof Exp] -> ExpSet
  (define (eval1-prim o args)
    (if (andmap value? args) {δ o args}
        (let ([z (split-at (compose not value?) args)])
          {exp-set-map (λ (v)
                         (prim-app o (combine (replace v z))))
                       (eval1 (focus z))})))
  
  ;; eval1-mon : Label Label Label Contract Exp -> ExpSet
  (define (eval1-mon h f g c e)
    (match e
      [(value u cs)
       {single
        (match (verify e c)
          ['Proved e]
          ['Refuted (blame/ f h)]
          ['Neither
           (match c
             [(flat/c p) (if/ (app p e) (refine e c) (blame/ f h))]
             [(func/c C x t D)
              (value (lam x t (mon h f g D (app e (mon h g f C x)))) '{})])])}]
      [else {exp-set-map (λ (v) (mon h f g c v)) (eval1 e)}]))
  
  (match e
    [(value u cs) {single e}]
    [(blame/ l1 l2) {single e}]
    [(app e1 e2) (eval1-app e1 e2)]
    [(rec f t e) {single (subst f (rec f t e) e)}]
    [(if/ e1 e2 e3) (eval1-if e1 e2 e3)]
    [(prim-app o args) (eval1-prim o args)]
    [(mon h f g c e) (eval1-mon h f g c e)]
    ; good programs can't reach here
    [else (error "eval1: unexpected: " e)]))

;; verify : Value Contract -> Verified
;; Verified := 'Proved | 'Refuted | 'Neither
(define (verify v c)
  (if (ormap (curry con=? c) (value-refinements v))
      'Proved
      'Neither))

;; fix : (x -> x) x (x x -> Boolean) -> x
(define (fix f x =?)
  ;; go : x x -> x
  (define (go x y)
    (if (=? x y) x (go y (f y))))
  (go x (f x)))



;;;;; tests

;; test evaluation
(for-each
 (λ (case)
   (match case
     [`(,e ,a ,l) (test-true
                   l
                   (exp-set=? (eval* (read-exp e)) (map read-exp a)))]))
 `([,ev? {,ev?} "ev?"]
   [,ap00 {2} "ap00"]
   [(,tri 3) {6} "tri"]))