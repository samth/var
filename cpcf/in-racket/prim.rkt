#lang racket
(require "lang.rkt")
(require "env.rkt")

(provide
 (contract-out
  [∆ (symbol? symbol? . -> . exp?)]
  [p⇒? (pred? pred? . -> . verified?)])
 pred? C/ANY C/NUM C/REAL C/STR)

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
   [('+ `(,(CLO (? number? x) _) ,(CLO (? number? y) _)) Γ)
    {set (CLO (+ x y) ρ0 O0)}]))

;; ∆ : Symbol -> CON
(define ∆c
  (hash
   ;; operators
   '+ (c: '[num? num? → num?])
   '- (c: '[num? num? → num?])
   '* (c: '[num? num? → num?])
   '/ (c: '[(∧ num? non-zero?) num? → num?])
   
   ))

(define ∆preds
  (hash
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

(define (∆ caller x)
  (cond
    [(hash-has-key? ∆c x) (MON '∆ '∆ caller (hash-ref ∆c x) (PRIM x))]
    [(hash-has-key? ∆preds x)
     (match (hash-ref ∆preds x)
       [#f (PRED x)]
       [c (MON '∆ '∆ caller c (PRED x))])]
    [else (error "Unknown primitive identifier:" x)]))

;; primitive, type-like predicates
(define (pred? x)
  (or (PRED? x)
      (STRUCT-P? x)))

;; checks whether first predicate implies/precludes second
(define p⇒?
  (match-lambda**
   [(_ [PRED 'tt]) 'Proved]
   [(p p) 'Proved]
   [([PRED 'false?] [PRED 'true?]) 'Refuted]
   [(_ [PRED 'true?]) 'Proved]
   [([PRED (or 'zero? 'non-zero? 'int? 'real?)] [PRED 'num?]) 'Proved]
   [([PRED 'zero?] [PRED 'int?]) 'Proved]
   [([PRED (or 'zero? 'non-zero? 'int?)] [PRED 'real?]) 'Proved]
   [([PRED x] [PRED y])
    (if (ormap (λ (group)
                 (and (member x group) (member y group)))
               '({true? false?}
                 {false? proc? str? num?}
                 {false? proc? str? real?}
                 {false? proc? str? int?}))
        'Refuted
        'Neither)]
   ;; only 'simple' primitive predicates can overlap at this point
   [(_ _) 'Refuted]))