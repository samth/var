#lang racket
(require racket/contract)
(require "env.rkt")

(provide
 (contract-out
  [struct PROG ([modules modls?] [main exp?])]
  [struct MODL ([name symbol?] [exports (hash/c symbol? CON?)]
                               [bindings (hash/c symbol? exp?)])]
  [struct M-REF ([caller symbol?] [callee symbol?] [name symbol?])]
  [struct AP ([func exp?] [args (listof exp?)])]
  [struct IF ([test exp?] [then exp?] [else exp?])]
  [struct MU ([x symbol?] [body exp?])]
  [struct MON ([lo symbol?] [l+ symbol?] [l- symbol?] [con CON?] [exp exp?])]
  [struct BLM ([who symbol?] [whom symbol?])]
  [struct LAM ([xs (listof symbol?)] [body exp?] [var-arg? boolean?])]
  [struct OPQ ([refinements (listof CC?)])]
  [struct CLO ([e exp?] [ρ env?] [O env?])]
  [struct C-STRUCT ([tag symbol?] [fields (listof C?)])]
  [struct C-MON ([lo symbol?] [l+ symbol?] [l- symbol?] [con CC?] [exp exp?])]
  [con? (any/c . -> . boolean?)]
  [struct FLAT/C ([exp exp?])]
  [struct OR/C ([c1 CON?] [c2 CON?])]
  [struct AND/C ([c1 CON?] [c2 CON?])]
  [struct STRUCT/C ([tag symbol?] [fields (listof CON?)])]
  [struct FUNC/C ([c1 (listof (list/c symbol? CON?))] [c2 CON?] [var-arg? boolean?])]
  [struct MU/C ([x symbol?] [body CON?])]
  [struct CC ([c CON?] [ρ env?] [O env?])]
  [struct STRUCT-MK ([tag symbol?] [field-count integer?])]
  [struct STRUCT-AC ([tag symbol?] [field-count integer?] [index integer?])]
  [struct STRUCT-P ([tag symbol?] [field-count integer?])]
  [CONS val?] [CONS? val?] [CAR val?] [CDR val?]
  [∨ (verified? verified? . -> . verified?)]
  [∧ (verified? verified? . -> . verified?)]
  [¬ (verified? . -> . verified?)])
 verified? modls-has? modl-defines? modl-exports? C?
 base? exp? val? V? modls? ∅)

;; Program = (prog Modules Exp)
(struct PROG (modules main) #:transparent)

;; Module = (modl Symbol [Hashtable Symbol Value′] [Hashtable Symbol Contract])
(struct MODL (name exports bindings) #:transparent)
;; Modules = [Hashtable Symbol Module]
(define modls? (hash/c symbol? MODL?))
;; Module Symbol -> Boolean
(define (modl-exports? m x)
  (hash-has-key? (MODL-exports m) x))
(define (modl-defines? m x)
  (hash-has-key? (MODL-bindings m) x))
;; Modules Symbol -> Boolean
(define modls-has? hash-has-key?)

;; Exp = .....
(define (exp? x)
  (or (EXP? x) (symbol? x) (val? x)))
(define (ans? x)
  (or (ANS? x) (val? x)))
(struct EXP () #:transparent)
(struct ANS EXP () #:transparent)
(struct M-REF EXP (caller callee name) #:transparent)
(struct AP EXP (func args) #:transparent)
(struct IF EXP (test then else) #:transparent)
(struct MU EXP (x body) #:transparent)
(struct MON EXP (lo l+ l- con exp) #:transparent)
(struct BLM ANS (who whom) #:transparent)

;; Value = ...
(define (val? x)
  (or (LAM? x) (OPQ? x) (base? x)
      (STRUCT-MK? x) (STRUCT-AC? x) (STRUCT-P? x)))
(define (base? x)
  (or (number? x) (string? x) (boolean? x)))
(struct LAM ANS (xs body var-arg?) #:transparent)
(struct OPQ ANS (refinements) #:transparent)
;; special operators for structs
(struct STRUCT-MK ANS (tag field-count) #:transparent)
(struct STRUCT-AC ANS (tag field-count index) #:transparent)
(struct STRUCT-P ANS (tag field-count) #:transparent)

;; Closures
(struct C () #:transparent)
(struct CLO C (e ρ O) #:transparent)
(struct C-STRUCT (tag fields) #:transparent)
(struct C-MON (lo l+ l- con exp) #:transparent)
(define (V? x)
  (match x
    [(CLO e _ρ _O) (val? e)]
    [(C-STRUCT _ xs) (andmap V? xs)]
    [(C-MON _o _+ _- (CC (FUNC/C _c1 _c2 _var?) _ρ _O) c) (V? c)]
    [_ #f]))

;; Contracts
(struct CON () #:transparent)
(struct FLAT/C CON (exp) #:transparent)
(struct OR/C CON (c1 c2) #:transparent)
(struct AND/C CON (c1 c2) #:transparent)
(struct STRUCT/C CON (tag fields) #:transparent)
(struct FUNC/C CON (c1 c2 var-arg?) #:transparent)
(struct MU/C CON (x body) #:transparent)
(define con? CON?)
;; Closed Contract
(struct CC (c ρ O) #:transparent)

(define verified?
  (match-lambda
    [(or 'Proved 'Refuted 'Neither) #t]
    [_ #f]))

(define ∅ (set))

;; cons stuff
(define CONS (STRUCT-MK 'cons 2))
(define CONS? (STRUCT-P 'cons 2))
(define CAR (STRUCT-AC 'cons 2 0))
(define CDR (STRUCT-AC 'cons 2 1))

;; and/or operators on verification result
(define ∨
  (match-lambda*
    [(or `(Proved ,_) `(,_ Proved)) 'Proved]
    [(or `(Neither ,_) `(,_ Neither)) 'Neither]
    [_ 'Refuted]))
(define ∧
  (match-lambda*
    [`(Proved Proved) 'Proved]
    [(or `(Refuted ,_) `(,_ Refuted)) 'Refuted]
    [_ 'Neither]))
(define ¬
  (match-lambda
    ['Proved 'Refuted]
    ['Refuted 'Proved]
    [_ 'Neither]))