#lang racket
(require redex) ; variable-not-in
(require rackunit)
(require racket/contract)

(require "env.rkt")

(provide
 
 (contract-out
  [struct ref ([distance natural?])]
  [struct val ([pre pre-val?] [refinements (set/c contract-clo?)])]
  [struct opaque ([type type?])]
  
  [struct lam ([type type?] [body exp?])]
  [struct app ([func exp?] [arg exp?])]
  [struct rec ([type type?] [body exp?])]
  [struct if/ ([test exp?] [then exp?] [else exp?])]
  [struct mon ([orig label?] [pos label?] [neg label?]
                             [con contract/?] [exp exp?])]
  [struct prim-app ([op op?] [args (listof exp?)])]
  [struct blame/ ([violator label?] [violatee label?])]
  
  [struct flat/c ([exp exp?])]
  [struct func/c ([dom contract/?] [type type?] [rng contract/?])]
  [struct consc ([car contract/?] [cdr contract/?])]
  [struct orc ([left contract/?] [right contract/?])]
  [struct andc ([left contract/?] [right contract/?])]
  [struct rec/c ([type type?] [body contract/?])]
  [struct con-ref ([distance natural?])]
  
  ;; hiding closure constructors would make it tedious due to lack of
  ;; pattern matching. But client is expected to use close instead of
  ;; 'exp-clo', and 'close-contract' instead of 'contract-clo'
  [struct exp-clo ([exp exp?] [env env?])]
  [struct mon-fn-clo ([orig label?] [pos label?] [neg label?]
                                    [con (struct/c contract-clo func/c? env?)]
                                    [exp clo?])]
  [struct cons-clo ([car clo?] [cdr clo?])]
  [struct contract-clo ([con contract/?] [env env?])]
  [clo? (any/c . -> . boolean?)]
  [close (exp? env? . -> . clo?)]
  [close-contract (contract/? env? . -> . contract-clo?)]
  [val-closure? (any/c . -> . boolean?)]
  
  ;; Type := BaseType | FuncType | ListType | ConType
  ;; BaseType = 'Num | 'Bool | '⊥
  [struct func-type ([from type?] [to type?])]
  [struct list-type ([of type?])]
  [struct con-type ([of type?])]
  
  [shift (natural? exp? . -> . exp?)]
  
  [δ (op? (listof clo?) . -> . (set/c clo?))]
  [type-check (exp? . -> . type-result?)]
  
  [read-exp (s-exp? . -> . exp?)]
  [show-exp (exp? . -> . s-exp?)]
  [show-type (type-result? . -> . s-exp?)]
  
  [exp? (any/c . -> . boolean?)]
  [answer? (any/c . -> . boolean?)]
  [pre-val? (any/c . -> . boolean?)]
  [label? (any/c . -> . boolean?)]
  [op? (any/c . -> . boolean?)]
  [type? (any/c . -> . boolean?)]
  [base-type? (any/c . -> . boolean?)]
  [type-result? (any/c . -> . boolean?)]
  [s-exp? (any/c . -> . boolean?)])
 
 ∅)

;; ∅ : Setof x
;; (eq? (set) (set)) = #f, and we have a lot of empty sets around,
;; so I guess this might be useful. It looks nicer anyway.
(define ∅ (set))

;; s-exp? : Any -> Boolean
(define s-exp? any/c) ; TODO

(struct exp () #:transparent)
(struct answer exp () #:transparent)
;; Val := (val Preval [Listof ContractClosure])
(struct val answer (pre refinements) #:transparent)
;; Ref := (ref Natural)
(struct ref exp (distance) #:transparent)
;; App := (app Exp Exp)
(struct app exp (func arg) #:transparent)
;; Rec := (rec Type Exp)
(struct rec exp (type body) #:transparent)
;; If := (if/ Exp Exp Exp)
(struct if/ exp (test then else) #:transparent)
;; PrimApp := (prim-app Op [Listof Exp])
(struct prim-app exp (op args) #:transparent)
;; Mon := (mon Label Label label Contract Exp)
(struct mon exp (orig pos neg con exp) #:transparent)

;; Blame := (blame/ Label Label)
(struct blame/ answer (violator violatee) #:transparent)

;; PreVal := Opaque | Number | Boolean | String | Lambda
(define (pre-val? x)
  (or (number? x) (boolean? x) (string? x) (opaque? x) (lam? x) (eq? 'nil x)))
;; Opaque := (opaque Type)
(struct opaque (type) #:transparent)
;; Lambda := (lambda Type Exp)
(struct lam (type body) #:transparent)
;; pre-val? : Any -> Boolean

;; Closure := ExpClosure | MonFnClosure | ConsClosure
(struct clo () #:transparent)
;; ExpClosure := (exp-clo Exp Env)
(struct exp-clo clo (exp env) #:transparent)
;; MonFnClosure := (mon-fn-clo Label Label Label ContractClosure Closure)
(struct mon-fn-clo clo (orig pos neg con exp) #:transparent)
;; ConsClosure := (cons-clo Closure Closure)
(struct cons-clo clo (car cdr) #:transparent)

;; close : Exp Env -> Closure
(define (close exp en)
  (exp-clo exp (env-restrict (free-vars exp) en)))

;; val-closure? : Closure -> Boolean
;; checks whether closure represents a value
(define (val-closure? clo)
  (or (and (exp-clo? clo) (val? (exp-clo-exp clo)))
      (mon-fn-clo? clo)
      (cons-clo? clo)))

;; checks whether symbol names a primitive op
(define (op? o)
  (hash-has-key? ops o))

;; label? : Any -> Boolean
(define label? symbol?)

;; Contract := FlatContract | FuncContract | ConsContract
;;           | OrContract | AndContract | RecContract
(struct contract/ () #:transparent)
(struct flat/c contract/ (exp) #:transparent)
(struct func/c contract/ (dom type rng) #:transparent)
(struct consc contract/ (car cdr) #:transparent)
(struct orc contract/ (left right) #:transparent)
(struct andc contract/ (left right) #:transparent)
(struct rec/c contract/ (type body) #:transparent)
(struct con-ref contract/ (distance) #:transparent)

;; ContractClosure = (contract-clo Contract [Env Val])
(struct contract-clo (con env) #:transparent)

;; close-contract : Contract Env -> ContractClosure
(define (close-contract con en)
  (contract-clo con (env-restrict (con-free-vars con) en)))

;; type? : Any -> Boolean
;; Type = BaseType | (func-type Type Type) | (con-type Type) | (list-type type)
(define (type? x)
  (or (base-type? x) (func-type? x) (con-type? x) (list-type? x)))
(struct func-type (from to) #:transparent)
(struct con-type (of) #:transparent)
(struct list-type (of) #:transparent)

;; base-type? : Any -> Boolean
;; BaseType = 'Num | 'Bool | String | '⊥
(define (base-type? x)
  (member x '(Num Bool String ⊥)))

;; TypeResult = Type | TypeError
(define (type-result? x)
  (or (type? x) (equal? x 'TypeError)))

;; δ : Op [Listof Closure] -> [Setof Closure]
;; applies primitive op
(define (δ o xs)
  (apply (third (hash-ref ops o)) xs))

;; extend : (Type* -> TypeResult) TypeResult* -> TypeResult
;; extends function's range from Type* to TypeResult*
;; returns 'TypeError if any argument is
(define (extend f . maybeTypes)
  (if (ormap (curry equal? 'TypeError) maybeTypes)
      'TypeError
      (apply f maybeTypes)))

;; Type Type -> TypeResult
;; returns most specific supertype
(define (⊔ t1 t2)
  (match `(,t1 ,t2)
    [`(,t ,t) t]
    [`(⊥ ,t) t]
    [`(,t ⊥) t]
    [`(,(func-type x y1) ,(func-type x y2)) (func-type x (⊔ y1 y2))]
    [`(,(list-type t1) ,(list-type t2)) (list-type (⊔ t1 t2))]
    [`(,(con-type t1) ,(con-type t2)) (con-type (⊔ t1 t2))]
    [else 'TypeError]))

;; ops : Symbol → (List (Listof Type) Type Function)
;; primitive ops' types and implementations
(define ops
  (local
    (;; closures for booleans
     [define TRUE (exp-clo (val #t ∅) ρ0)]
     [define FALSE (exp-clo (val #f ∅) ρ0)]
     [define ABSTRACT-NUM (exp-clo (val (opaque 'Num) ∅) ρ0)]
     [define ABSTRACT-STR (exp-clo (val (opaque 'String) ∅) ρ0)]
     
     ;; checks for function type (List _ -> Bool)
     [define check:list→bool
       (match-lambda
         [`(,(list-type t)) 'Bool]
         [_ 'TypeError])]
     
     ;; check-real : (Real Real -> Bool) Symbol -> (Num Num -> Bool or Blame)
     ;; checks for real arguments before applying primitive function
     [define (check-real op name)
       (λ (x y)
         (if (and (real? x) (real? y))
             (op x y)
             (blame/ '† name)))]
     
     ;; prim : Symbol [Listof Type] Type Proc
     ;;     -> [List ([Listof Type] -> TypeResult) (Closure* -> Closure)]
     (define (prim name param-types res-type proc #:partial [partial? #f])
       `(,(length param-types)
         ,(λ (arg-types)
            (if (equal? param-types arg-types) res-type 'TypeError))
         ,(local ;; TODO: how to define λ with var-args?
            ([define (op1 . xs)
               (if (andmap exp-clo? xs)
                   (let ([pre-vals (map (compose val-pre exp-clo-exp) xs)])
                     (if (ormap opaque? pre-vals)
                         (set-union
                          (if partial? {set (exp-clo (blame/ '† name) ρ0)} ∅)
                          (match res-type
                            ['Num {set ABSTRACT-NUM}]
                            ['Bool {set TRUE FALSE}]
                            ['String {set ABSTRACT-STR}]))
                         {set (exp-clo (let ([a (apply proc pre-vals)])
                                         (if (blame/? a) a (val a ∅)))
                                       ρ0)}))
                   {set (exp-clo (blame/ '† name) ρ0)})])
            op1))))
    
    (hash
     'not (prim 'not '(Bool) 'Bool not)
     'zero? (prim 'zero? '(Num) 'Bool zero?)
     'non-neg? (prim 'non-neg? '(Num) 'Bool
                     (and/c real? (compose not negative?)))
     'even? (prim 'even? '(Num) 'Bool (and/c integer? even?))
     'odd? (prim 'odd? '(Num) 'Bool (and/c integer? odd?))
     'prime? (prim 'prime? '(Num) 'Bool
                   (λ (n) (if (member n '(2 3 5 7 11 13) #t #f) #t #f)))
     'true? (prim 'true? '(Bool) 'Bool (compose not false?))
     'false? (prim 'false? '(Bool) 'Bool false?)
     'sqrt (prim 'sqrt '(Num) 'Num sqrt)
     '+ (prim '+ '(Num Num) 'Num +)
     '- (prim '- '(Num Num) 'Num -)
     '* (prim '* '(Num Num) 'Num *)
     '= (prim '= '(Num Num) 'Bool =)
     '≠ (prim '≠ '(Num Num) 'Bool (compose not =))
     '< (prim '< '(Num Num) 'Bool (check-real < '<) #:partial #t)
     '≤ (prim '≤ '(Num Num) 'Bool (check-real <= '≤) #:partial #t)
     '> (prim '> '(Num Num) 'Bool (check-real > '>) #:partial #t)
     '≥ (prim '≥ '(Num Num) 'Bool (check-real >= '≥) #:partial #t)
     '++ (prim '++ '(String String) 'String string-append)
     'str=? (prim 'str=? '(String String) 'Bool string=?)
     'str≠? (prim 'str≠? '(String String) 'Bool (compose not string=?))
     'str<? (prim 'str<? '(String String) 'Bool string<?)
     'str≤? (prim 'str≤? '(String String) 'Bool string<=?)
     'str>? (prim 'str>? '(String String) 'Bool string>?)
     'str≥? (prim 'str≥? '(String String) 'Bool string>=?)
     'str-length (prim 'str-length '(String) 'Num string-length)
     'substring (prim 'substring '(String Num Num) 'String
                      (λ (s start end)
                        (if (and (integer? start) (integer? end)
                                 (<= 0 start end (string-length s)))
                            (substring s start end)
                            (blame/ '† 'substring)))
                      #:partial #t)
     'cons `(2
             ,(match-lambda
                [`(,t1 ,(list-type t2)) (extend list-type (⊔ t1 t2))]
                [_ 'TypeError])
             ,(compose set cons-clo))
     'nil? `(1
             ,check:list→bool
             ,(match-lambda
                [(exp-clo (val 'nil cs) ρ) {set TRUE}]
                [(exp-clo (val (opaque (list-type t)) cs) ρ) {set TRUE FALSE}]
                [_ {set FALSE}]))
     'cons? `(1
              ,check:list→bool
              ,(match-lambda
                 [(exp-clo (val (opaque (list-type t)) cs) ρ) {set TRUE FALSE}]
                 [(cons-clo c1 c2) {set TRUE}]
                 [_ {set FALSE}]))
     'car `(1
            ,(match-lambda
               [`(,(list-type t)) t]
               [_ 'TypeError])
            ,(match-lambda
               [(cons-clo c1 c2) {set c1}]
               [(exp-clo (val (opaque (list-type t)) cs) ρ)
                {set (exp-clo (val (opaque t) ∅) ρ0)
                     (exp-clo (blame/ '† 'car) ρ0)}]
               [_ {set (exp-clo (blame/ '† 'car) ρ0)}]))
     'cdr `(1
            ,(match-lambda
               [`(,t) (if (list-type? t) t 'TypeError)]
               [_ 'TypeError])
            ,(match-lambda
               [(cons-clo c1 c2) {set c2}]
               [(exp-clo (val (opaque (list-type t)) cs) ρ)
                {set (exp-clo (val (opaque (list-type t)) ∅) ρ0)
                     (exp-clo (blame/ '† 'cdr) ρ0)}]
               [_ {set (exp-clo (blame/ '† 'cdr) ρ0)}])))))

;; op-impl : Symbol -> Function
(define (op-impl name)
  (third (hash-ref ops name)))

;; prim? : Any -> Boolean
(define (prim? name)
  (hash-has-key? ops name))

;; arity : Op -> Natural
(define (arity op-name)
  (first (hash-ref ops op-name)))

;; type-check : Exp -> TypeResult
(define (type-check e)
  
  ;; type-check-with : [Env TypeResult] Exp -> TypeResult
  (define (type-check-with tenv e)
    (match e
      [(ref d) (env-get-default d 'TypeError tenv)]
      [(val u cs) (match u
                    [(opaque t) t]
                    [(lam t b)
                     (extend func-type t
                             (type-check-with (env-extend t tenv) b))]
                    ['nil (list-type '⊥)]
                    [_ (cond
                         [(number? u) 'Num]
                         [(boolean? u) 'Bool]
                         [(string? u) 'String])])]
      [(blame/ l1 l2) '⊥]
      [(app f x) (extend type-app
                         (type-check-with tenv f)
                         (type-check-with tenv x))]
      [(rec t b) (type-check-with (env-extend t tenv) b)]
      [(if/ e1 e2 e3) (extend type-if
                              (type-check-with tenv e1)
                              (type-check-with tenv e2)
                              (type-check-with tenv e3))]
      [(prim-app o xs) (apply (curry extend (curry ∆ o))
                              (map (curry type-check-with tenv) xs))]
      [(mon h f g c e) (extend type-mon
                               (type-check-con-with tenv c)
                               (type-check-with tenv e))]))
  
  ;; type-check-con-with : [Env TypeResult] Contract -> TypeResult
  (define (type-check-con-with tenv c)
    (match c
      [(flat/c e) (match (type-check-with tenv e)
                    [(func-type t 'Bool) (extend con-type t)]
                    [else 'TypeError])]
      [(func/c dom t rng)
       (match `(,(type-check-con-with tenv dom)
                ,(type-check-con-with (env-extend t tenv) rng))
         [`(,(con-type t1) ,(con-type t2))
          (extend con-type (func-type t1 t2))]
         [else 'TypeError])]
      [(consc c1 c2) (match `(,(type-check-con-with tenv c1)
                              ,(type-check-con-with tenv c2))
                       [`(,(con-type t1) ,(con-type (list-type t2)))
                        (if (⊑ t2 t1) (con-type (list-type t1)) 'TypeError)]
                       [_ 'TypeError])]
      [(orc c1 c2) (extend ⊔ (type-check-con-with tenv c1)
                           (type-check-con-with tenv c2))]
      [(andc c1 c2) (extend ⊔ (type-check-con-with tenv c1)
                            (type-check-con-with tenv c2))]
      [(rec/c t c) (type-check-con-with (env-extend t tenv) c)]
      [(con-ref x) (env-get x tenv)]))
  
  ;; type-app : Type Type -> TypeResult
  (define (type-app f arg)
    (match f
      [(func-type dom rng) (if (⊑ arg dom) rng 'TypeError)]
      [else 'TypeError]))
  
  ;; type-if : Type Type Type -> TypeResult
  (define (type-if t1 t2 t3)
    (match t1
      ['Bool (⊔ t2 t3)]
      [else 'TypeError]))
  
  ;; type-mon : Type Type -> TypeResult
  (define (type-mon c e)
    (match `(,c ,e)
      [`(,(con-type t1) ,t2) (if (equal? t1 t2) t1 'TypeError)]
      [else 'TypeError]))
  
  ;; Type Type -> Boolean
  (define (⊑ t1 t2)
    (match `(,t1 ,t2)
      [`(,t ,t) #t]
      [`(⊥ ,t) #t]
      [`(,(func-type tx1 ty1) ,(func-type tx2 ty2))
       (and (⊑ tx2 tx1) (⊑ ty1 ty2))]
      [`(,(list-type t3) ,(list-type t4)) (⊑ t3 t4)]
      [`(,(con-type t3) ,(con-type t4)) (⊑ t3 t4)]
      [_ #f]))
  
  ;; ∆ : Op Type* -> TypeResult
  (define (∆ o . arg-types)
    ((second (hash-ref ops o)) arg-types))
  
  (type-check-with ρ0 e))

;; free-vars : Exp -> [Setof Natural]
(define (free-vars e)
  (vars≥ 0 e))
;; vars≥ : Exp -> [Setof Natural]
(define (vars≥ d e)
  (match e
    [(ref k) (if (>= k d) {set (- k d)} ∅)]
    [(val u cs) (match u
                  [(lam t b) (vars≥ (+ 1 d) b)]
                  [else ∅])]
    [(blame/ l1 l2) ∅]
    [(app e1 e2) (set-union (vars≥ d e1) (vars≥ d e2))]
    [(rec t b) (vars≥ (+ 1 d) b)]
    [(if/ e1 e2 e3) (set-union (vars≥ d e1) (vars≥ d e2) (vars≥ d e3))]
    [(prim-app o args) (apply set-union (map (curry vars≥ d) args))]
    [(mon h f g c e) (set-union (con-vars≥ d c) (vars≥ d e))]))
;; con-free-vars : Contract -> [Setof Natural]
(define (con-free-vars c)
  (con-vars≥ 0 c))
;; con-vars≥ : Natural Contract -> [Setof Natural]
(define (con-vars≥ d c)
  (match c
    [(flat/c e) (vars≥ d e)]
    [(func/c c1 t c2) (set-union (con-vars≥ d c1) (con-vars≥ (+ 1 d) c2))]
    [(consc c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(orc c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(andc c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(rec/c t c) (con-vars≥ (+ 1 d) c)]
    [(con-ref x) (if (>= x d) {set (- x d)} ∅)]))

;; read-exp : S-exp -> Exp
(define (read-exp s)
  (read-exp-with empty s))

;; read-con : S-exp -> Contract
(define (read-con s)
  (read-con-with empty s))

;; read-type : S-exp -> Type
(define (read-type s)
  (match s
    ['Num 'Num]
    ['Bool 'Bool]
    ['⊥ '⊥] ; just for debugging
    [`(,t1 → ,t2) (func-type (read-type t1) (read-type t2))]
    [`(List ,t) (list-type (read-type t))]
    [`(con ,t) (con-type (read-type t))]
    [else (error "invalid type form: " s)]))

;; read-con-with : [Listof Symbol] S-exp -> Contract
(define (read-con-with names s)
  (match s
    [`(flat ,e) (flat/c (read-exp-with names e))]
    [`(,c ↦ (λ (,x ,t) ,d))
     (if (symbol? x)
         (func/c (read-con-with names c)
                 (read-type t)
                 (read-con-with (cons x names) d))
         (error "function contract: expect symbol, given: " x))]
    [`(,c ↦ ,d)
     (let ([x (variable-not-in d 'z)]) ; desugar independent contract
       (read-con-with names `(,c ↦ (λ (,x Num) ,d))))]
    [`(cons/c ,c ,d) (consc (read-con-with names c) (read-con-with names d))]
    [`(,c ∨ ,d) (orc (read-con-with names c) (read-con-with names d))]
    [`(,c ∧ ,d) (andc (read-con-with names c) (read-con-with names d))]
    [`(μ (,x ,t) ,c) (rec/c (read-type t) (read-con-with (cons x names) c))]
    [x (if (symbol? x)
           (con-ref (name-distance x names))
           (error "invalid contract form: " x))]))

;; read-exp-with : [Listof Symbol] S-exp -> Exp
(define (read-exp-with names s)
  
  ;; read-and : [Listof S-exp] -> Exp
  (define (read-and terms)
    (match terms
      [`(,t1 ,t2 ,ts ...) (if/ (read-exp-with names t1)
                               (read-and (rest terms))
                               (val #f ∅))]
      [`(,t) (read-exp-with names t)]
      [`() (val #t ∅)]))
  
  ;; read-or : [Listof S-exp] -> Exp
  (define (read-or terms)
    (match terms
      [`(,t1 ,t2 ,ts ...) (if/ (read-exp-with names t1)
                               (val #t ∅)
                               (read-or (rest terms)))]
      [`(,t) (read-exp-with names t)]
      [`() (val #f ∅)]))
  
  (match s
    [`(• ,t) (val (opaque (read-type t)) ∅)]
    [`(λ (,x ,t) ,s) (if (symbol? x)
                         (val (lam (read-type t)
                                   (read-exp-with (cons x names) s))
                              ∅)
                         (error "λ: expect symbol, given: " x))]
    [`(blame ,f ,g) (if (and (symbol? f) (symbol? g))
                        (blame/ f g)
                        (error "blame: expect symbols, given: " f g))]
    [`(μ (,f ,t) ,s) (if (symbol? f)
                         (rec (read-type t) (read-exp-with (cons f names) s))
                         (error "μ: expect symbol, given: " f))]
    [`(if ,s1 ,s2 ,s3) (if/ (read-exp-with names s1)
                            (read-exp-with names s2)
                            (read-exp-with names s3))]
    [`(mon ,h ,f ,g ,c ,e)
     (if (andmap symbol? `(,h ,f ,g))
         (mon h f g (read-con-with names c) (read-exp-with names e))
         (error "mon: expect symbols, given: " h f g))]
    [`(and ,terms ...) (read-and terms)]
    [`(or ,terms ...) (read-or terms)]
    [`(,s0 ,ss ...)
     (if (prim? s0)
         (if (= (arity s0) (length ss))
             (prim-app s0 (map (curry read-exp-with names) ss))
             (error "arity mismatch for " s0))
         (if (= 1 (length ss))
             (app (read-exp-with names s0) (read-exp-with names (first ss)))
             (error "illegal application form " s)))]
    [x (cond
         [(pre-val? x) (val x ∅)]
         [(symbol? x) (ref (name-distance x names))]
         [else (error "invalid expression form: " x)])]))

;; show-exp : Exp -> S-exp
(define (show-exp e)
  
  ;; with-pool : [Listof Symbol] -> [Listof Symbol] -> Symbol
  (define (with-pool pool)
    (λ (used-names)
      (match (filter (λ (n) (not (member n used-names))) pool)
        [(cons name names) name]
        [empty (variable-not-in used-names (first pool))])))
  ;; new-var-name, new-fun-name : [Listof Symbol] -> Symbol
  (define new-var-name (with-pool '(x y z a b c w u v m n)))
  (define new-fun-name (with-pool '(f g h p q)))
  
  ;; show-exp-with : [Listof Symbol] -> S-exp
  (define (show-exp-with names e)
    (match e
      [(ref d) (list-ref names d)] ;; closed expressions can't cause error
      [(val u _)
       (match u
         [(opaque t) `(• ,(show-type t))]
         [(lam t b) 
          (let ([x ((if (func-type? t) new-fun-name new-var-name) names)])
            `(λ (,x ,(show-type t))
               ,(show-exp-with (cons x names) b)))]
         [c c])]
      [(blame/ l1 l2) `(blame l1 l2)]
      [(app f x) `(,(show-exp-with names f) ,(show-exp-with names x))]
      [(rec t b)
       (let ([f (new-fun-name names)])
         `(μ (,f ,(show-type t))
             ,(show-exp-with (cons f names) b)))]
      [(if/ e1 e2 e3) `(if ,@(map (curry show-exp-with names) `(,e1 ,e2 ,e3)))]
      [(prim-app o args) `(,o ,@(map (curry show-exp-with names) args))]
      [(mon h f g c e) `(mon ,h ,f ,g
                             ,(show-con-with names c)
                             ,(show-exp-with names e))]))
  
  ;; show-con-with : [Listof Symbol] Contract -> S-exp
  (define (show-con-with names c)
    (match c
      [(flat/c e) `(flat ,(show-exp-with names e))]
      [(func/c c t d)
       `(,(show-con-with names c)
         ↦
         ,(let ([x (new-var-name names)])
            `(λ (,x ,(show-type t)) ,(show-con-with (cons x names) d))))]
      [(consc c d) `(consc ,(show-con-with names c) ,(show-con-with names d))]
      [(orc c d) `(,(show-con-with names c) ∨ ,(show-con-with names d))]
      [(andc c d) `(,(show-con-with names c) ∧ ,(show-con-with names d))]
      [(rec/c t c) (let ([x (new-var-name names)])
                     `(μ (,x ,(show-type t)) ,(show-con-with (cons x names) c)))]
      [(con-ref d) (list-ref names d)]))
  
  (show-exp-with empty e))

;; show-type : TypeResult -> S-exp
(define (show-type t)
  (match t
    [(func-type dom rng) `(,(show-type dom) → ,(show-type rng))]
    [(list-type t) `(List ,(show-type t))]
    [(con-type t) `(con ,(show-type t))]
    [t t]))

;; name-distance : Symbol [Listof Symbol] -> Natural
(define (name-distance x xs)
  ;; go : Natural [Listof Symbol] -> Natural
  (define (go pos xs)
    (match xs
      [(cons z zs) (if (equal? z x) pos (go (+ 1 pos) zs))]
      [empty (error "expression not closed, unbound variable: " x )]))
  (go 0 xs))

;; shift : Natural Exp -> Exp
;; shifts free variables in expression by given number
(define (shift d e)
  
  ;; shift-at : Natural Exp -> Exp
  (define (shift-at depth e)
    (match e
      [(ref x) (if (>= x depth) (ref (+ x d)) e)]
      [(val u cs)
       (match u
         [(lam t b) (val (lam t (shift-at (+ 1 depth) b)) cs)]
         [_ e])]
      [(blame/ l1 l2) e]
      [(app e1 e2) (app (shift-at depth e1) (shift-at depth e2))]
      [(rec t b) (rec t (shift-at (+ 1 depth) b))]
      [(if/ e1 e2 e3)
       (if/ (shift-at depth e1) (shift-at depth e2) (shift-at depth e3))]
      [(prim-app o xs) (prim-app o (map (curry shift-at depth) xs))]
      [(mon h f g c e) (mon h f g (shift-con-at depth c) (shift-at depth e))]))
  
  ;; shift-con-at : Natural Contract -> Contract
  (define (shift-con-at depth c)
    (match c
      [(flat/c e) (flat/c (shift-at depth e))]
      [(func/c c1 t c2)
       (func/c (shift-con-at depth c1) t (shift-con-at (+ 1 depth) c2))]
      [(consc c1 c2) (consc (shift-con-at depth c1) (shift-con-at depth c2))]
      [(orc c1 c2) (orc (shift-con-at depth c1) (shift-con-at depth c2))]
      [(andc c1 c2) (andc (shift-con-at depth c1) (shift-con-at depth c2))]
      [(rec/c t c1) (rec/c t (shift-con-at (+ 1 depth) c1))]
      [(con-ref x) (if (>= x depth) (con-ref (+ x d)) c)]))
  
  (shift-at 0 e))