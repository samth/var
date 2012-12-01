#lang racket
(require racket/contract)
(require "env.rkt")
(require "nd.rkt")

(provide
 (contract-out
  [struct PROG ([modules modls?] [main exp?])]
  [struct MODL ([name symbol?] [exports (hash/c symbol? CON?)]
                               [bindings (hash/c symbol? exp?)])]
  [struct M-REF ([caller symbol?] [callee symbol?] [name symbol?])]
  [struct AP ([func exp?] [args (listof exp?)] [l symbol?])]
  [struct IF ([test exp?] [then exp?] [else exp?])]
  [struct MU ([x symbol?] [body exp?])]
  [struct MON ([lo symbol?] [l+ symbol?] [l- symbol?] [con CON?] [exp exp?])]
  [struct BLM ([who symbol?] [whom symbol?])]
  [struct PRIM ([x symbol?])]
  [struct PRED ([x symbol?])]
  [struct LAM ([xs (listof symbol?)] [body exp?] [var-arg? boolean?])]
  [struct OPQ ([refinements (listof CC?)])]
  [struct CLO ([e exp?] [ρ env?])]
  [struct C-STRUCT ([tag symbol?] [fields (listof C?)])]
  [struct C-MON ([lo symbol?] [l+ symbol?] [l- symbol?] [con CC?] [exp exp?])]
  [AND (() () #:rest (listof exp?) . ->* . exp?)]
  [OR ((symbol?) () #:rest (listof exp?) . ->* . exp?)]
  [con? (any/c . -> . boolean?)]
  [struct FLAT/C ([exp exp?])]
  [struct OR/C ([c1 CON?] [c2 CON?])]
  [struct AND/C ([c1 CON?] [c2 CON?])]
  [struct STRUCT/C ([tag symbol?] [fields (listof CON?)])]
  [struct FUNC/C ([c1 (listof (list/c symbol? CON?))] [c2 CON?] [var-arg? boolean?])]
  [struct MU/C ([x symbol?] [body CON?])]
  [struct REF/C ([x symbol?])]
  [struct CC ([c CON?] [ρ env?])]
  [struct STRUCT-MK ([tag symbol?] [field-count integer?])]
  [struct STRUCT-AC ([tag symbol?] [field-count integer?] [index integer?])]
  [struct STRUCT-P ([tag symbol?] [field-count integer?])]
  [struct Π ([accs (listof STRUCT-AC?)] [x symbol?])]
  [struct VO ([v (or/c C? CC?)] [o π?])]
  
  [CONS val?] [CONS? val?] [CAR val?] [CDR val?]
  [close ((or/c exp? con?) env? . -> . (or/c C? CC?))]
  
  [FV (exp? . -> . (set/c symbol?))]
  
  [∨ (() () #:rest (listof verified?) . ->* . verified?)]
  [∧ (() () #:rest (listof verified?) . ->* . verified?)]
  [v¬ (verified? . -> . verified?)])
 verified? modls-has? modl-defines? modl-exports? C? π?
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
(struct AP EXP (func args l) #:transparent)
(struct IF EXP (test then else) #:transparent)
(struct MU EXP (x body) #:transparent)
(struct MON EXP (lo l+ l- con exp) #:transparent)
(struct BLM ANS (who whom) #:transparent)

;; Value = ...
(define (val? x)
  (or (LAM? x) (OPQ? x) (base? x) (PRIM? x)
      (STRUCT-MK? x) (STRUCT-AC? x) (STRUCT-P? x)))
(define (base? x)
  (or (number? x) (string? x) (boolean? x)))
(struct LAM ANS (xs body var-arg?) #:transparent)
(struct OPQ ANS (refinements) #:transparent)
;; special operators for structs
(struct STRUCT-MK ANS (tag field-count) #:transparent)
(struct STRUCT-AC ANS (tag field-count index) #:transparent)
(struct STRUCT-P ANS (tag field-count) #:transparent)
(struct PRIM ANS (x) #:transparent)
(struct PRED PRIM () #:transparent)

;; Closures
(struct C () #:transparent)
(struct CLO C (e ρ) #:transparent)
(struct C-STRUCT (tag fields) #:transparent)
(struct C-MON (lo l+ l- con exp) #:transparent)
(define (V? x)
  (match x
    [(CLO e _ρ) (val? e)]
    [(C-STRUCT _ xs) (andmap V? xs)]
    [(C-MON _o _+ _- (CC (FUNC/C _c1 _c2 _var?) _ρ) c) (V? c)]
    [_ #f]))

;; Contracts
(struct CON () #:transparent)
(struct FLAT/C CON (exp) #:transparent)
(struct OR/C CON (c1 c2) #:transparent)
(struct AND/C CON (c1 c2) #:transparent)
(struct STRUCT/C CON (tag fields) #:transparent)
(struct FUNC/C CON (c1 c2 var-arg?) #:transparent)
(struct MU/C CON (x body) #:transparent)
(struct REF/C CON (x) #:transparent)
(define con? CON?)
;; Closed Contract
(struct CC (c ρ) #:transparent)

(define AND
  (match-lambda*
    ['() #t]
    [`(,e) e]
    [`(,e1 ,e2 ...) (IF e1 (apply AND e2) #f)]))

(define (OR m . xs)
  (match xs
    ['() #f]
    [`(,e) e]
    [`(,e1 ,e2 ...) (AP
                     (LAM '(tmp)
                          (IF 'tmp 'tmp (apply (curry OR m) e2))
                          #f)
                     (list e1)
                     m)]))

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
(define (∨ . xs)
  (define v2
    (match-lambda*
      [(or `(Proved ,_) `(,_ Proved)) 'Proved]
      [(or `(Neither ,_) `(,_ Neither)) 'Neither]
      [_ 'Refuted]))
  (foldl v2 'Refuted xs))
(define (∧ . xs)
  (define ∧2
    (match-lambda*
      [`(Proved Proved) 'Proved]
      [(or `(Refuted ,_) `(,_ Refuted)) 'Refuted]
      [_ 'Neither]))
  (foldl ∧2 'Proved xs))
(define v¬
  (match-lambda
    ['Proved 'Refuted]
    ['Refuted 'Proved]
    [_ 'Neither]))

;; paths
(struct Π (accs x) #:transparent)
(define (π? x)
  (or (Π? x) (equal? x '∅)))

;; the valid thing that the run-time environment maps to
(struct VO (v o) #:transparent)

;; returns expression's free variables
(define FV
  (match-lambda
    [(AP f xs _) (set-union (FV f) (non-det FV xs))]
    [(IF e1 e2 e3) (set-union (FV e1) (FV e2) (FV e3))]
    [(MU x e) (set-remove (FV e) x)]
    [(MON _ _ _ c e) (set-union (FV-c c) (FV e))]
    [(LAM xs e _) (set-remove* (FV e) xs)]
    [(? symbol? x) {set x}]
    [(or [? val?] [? M-REF?] [? BLM?]) ∅]))
(define FV-c
  (match-lambda
    [(FLAT/C e) (FV e)]
    [(or (OR/C c1 c2) (AND/C c1 c2)) (set-union (FV-c c1) (FV-c c2))]
    [(STRUCT/C _ cs) (non-det FV-c cs)]
    [(FUNC/C `((,x ,c1) ...) c2 _)
     (set-union (non-det FV c1) (set-remove* (FV c2) x))]
    [(MU/C x c) (set-remove (FV-c c) x)]
    [(REF/C x) {set x}]))

;; closes expression/contract with environment, discarding unused variables
(define (close x ρ)
  (cond
    [(exp? x) (CLO x (env-restrict ρ (FV x)))]
    [(con? x) (CC x (env-restrict ρ (FV-c x)))]))

(define (set-remove* s l)
  (foldl (λ (x s) (set-remove s x)) s l))
