#lang racket
(require racket/contract)
(require "env.rkt")

(provide
 (contract-out
  [struct PROG ([modules modls?] [main exp?])]
  [struct MODL ([name symbol?] [exports (hash/c symbol? CON?)]
                               [bindings (hash/c symbol? exp?)])]
  [struct M-REF ([caller symbol?] [callee symbol?] [name symbol?])]
  [struct AP ([func exp?] [args exp?])]
  [struct IF ([test exp?] [then exp?] [else exp?])]
  [struct MU ([x symbol?] [body exp?])]
  [struct MON ([lo symbol?] [l+ symbol?] [l- symbol?] [con CON?] [exp exp?])]
  [struct BLM ([who symbol?] [whom symbol?])]
  [struct LAM ([xs (listof symbol?)] [body exp?] [var-arg? boolean?])]
  [struct OPQ ([refinements (listof CC?)])]
  [struct C-E ([e exp?] [ρ env?] [O env?])]
  [struct C-CONS ([car C?] [cdr C?])]
  [struct C-MON ([lo symbol?] [l+ symbol?] [l- symbol?] [con CC?] [exp exp?])]
  [struct FLAT/C ([exp exp?])]
  [struct OR/C ([c1 CON?] [c2 CON?])]
  [struct AND/C ([c1 CON?] [c2 CON?])]
  [struct CONS/C ([c1 CON?] [c2 CON?])]
  [struct FUNC/C ([c1 (listof (list/c symbol? CON?))] [c2 CON?] [var-arg? boolean?])]
  [struct CC ([c CON?] [ρ env?] [O env?])])
 
 exp? val? V? modls? ∆ prelude)

;; Program = (prog Modules Exp)
(struct PROG (modules main) #:transparent)

;; Module = (modl Symbol [Hashtable Symbol Value′] [Hashtable Symbol Contract])
(struct MODL (name exports bindings) #:transparent)
;; Modules = [Hashtable Symbol Module]
(define modls? (hash/c symbol? MODL?))

;; Exp = .....
(define (exp? x)
  (or (EXP? x) (val? x)))
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
  (or (LAM? x) (OPQ? x)
      (symbol? x) (number? x) (string? x) (boolean? x)))
(struct LAM ANS (xs body var-arg?) #:transparent)
(struct OPQ ANS (refinements) #:transparent)

;; Closures
(struct C () #:transparent)
(struct C-E C (e ρ O) #:transparent)
(struct C-CONS (car cdr) #:transparent)
(struct C-MON (lo l+ l- con exp) #:transparent)
(define (V? x)
  (match x
    [(C-E e _ρ _O) (val? e)]
    [(C-CONS c1 c2) (and (V? c1) (V? c2))]
    [(C-MON _o _+ _- (CC (FUNC/C _c1 _c2 _var?) _ρ _O) c) (V? c)]
    [_ #f]))

;; Contracts
(struct CON () #:transparent)
(struct FLAT/C CON (exp) #:transparent)
(struct OR/C CON (c1 c2) #:transparent)
(struct AND/C CON (c1 c2) #:transparent)
(struct CONS/C CON (c1 c2) #:transparent)
(struct FUNC/C CON (c1 c2 var-arg?) #:transparent)
;; Closed Contract
(struct CC (c ρ O) #:transparent)

;; primitive module
(define ∆
  (MODL '∆
        (hash)
        (hash)))

(define prelude
  (hash '∆ ∆))