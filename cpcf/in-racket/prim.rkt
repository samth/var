#lang racket
(require "lang.rkt")
(require "env.rkt")

(provide
 (contract-out
  [∆ (hash/c symbol? (or/c #f con?))]
  [prim? (symbol? . -> . boolean?)])
 C/ANY C/NUM C/REAL C/STR)

;; common basic contracts
(define C/ANY (FLAT/C 'tt))
(define C/NUM (FLAT/C 'num?))
(define C/REAL (FLAT/C 'real?))
(define C/STR (FLAT/C 'str?))

(define c:
  (letrec
   ([mk-c
     (match-lambda
       [`(∧ ,c1 ,c2) (AND/C (mk-c c1) (mk-c c2))]
       [`(∨ ,c1 ,c2) (OR/C (mk-c c1) (mk-c c2))]
       [p? (FLAT/C p?)])])
   (match-lambda
     [`(,c1 → ,c) (FUNC/C `([x ,(mk-c c1)]) (mk-c c) #f)]
     [`(,c1 ,c2 → ,c) (FUNC/C `([x ,(mk-c c1)] [y ,(mk-c c2)]) (mk-c c) #f)])))

;; primitive module
(define ρ0 env0)
(define O0 env0)

;; δ : Symbol [Listof [List V Path]] Γ -> [List Val Γ Path]
(define δ
  (match-lambda**
   
   ; +
   [('+ `(,(CLO (? number? x) _ _) ,(CLO (? number? y) _ _)) Γ)
    {set (CLO (+ x y) ρ0 O0)}]))

;; ∆ : Symbol -> CON
(define ∆
  (hash
   ;; operators
   '+ (c: '[num? num? → num?])
   '- (c: '[num? num? → num?])
   '* (c: '[num? num? → num?])
   '/ (c: '[(∧ num? non-zero?) num? → num?])
   
   ;; predicates
   'tt #f
   'true? #f
   'false? #f
   'bool? #f
   'str? #f
   'proc? #f
   'cons? #f
   'num? #f
   'real? #f
   'int? #f
   'zero? (c: '[num? → tt])
   'non-zero? (c: '[num? → tt])))

;; prim? : Symbol -> Boolean
(define (prim? x)
  (hash-has-key? ∆ x))