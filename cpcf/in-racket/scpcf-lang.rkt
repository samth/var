#lang racket
(require redex) ; variable-not-in
(require rackunit)
(require racket/contract)

(require "env.rkt")

(provide
 
 (contract-out
  [struct ref ([distance natural?])]
  [struct value ([pre pre-value?] [refinements (set/c contract-clo?)])]
  [struct opaque ([type type?])]
  
  [struct lam ([type type?] [body exp?])]
  [struct app ([func exp?] [arg exp?])]
  [struct rec ([type type?] [body exp?])]
  [struct if/ ([test exp?] [then exp?] [else exp?])]
  [struct mon ([orig label?] [pos label?] [neg label?]
                             [con contract/?] [exp exp?])]
  [struct prim-app ([op op?] [args (listof exp?)])]
  [struct blame/ ([violator label?] [violatee label?])]
  [struct cons/ ([car exp?] [cdr exp?])]
  [struct nil?/ ([of exp?])]
  [struct cons?/ ([of exp?])]
  [struct car/ ([of exp?])]
  [struct cdr/ ([of exp?])]
  
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
  
  ;; Type := BaseType | FuncType | ListType | ConType
  ;; BaseType = 'Num | 'Bool | '⊥
  [struct func-type ([from type?] [to type?])]
  [struct list-type ([of type?])]
  [struct con-type ([of type?])]
  
  [δ (op? (listof value?) . -> . (set/c answer?))]
  
  [type-check (exp? . -> . type-result?)]
  
  [read-exp (s-exp? . -> . exp?)]
  [show-exp (exp? . -> . s-exp?)]
  [show-type (type-result? . -> . s-exp?)]
  
  [exp? (any/c . -> . boolean?)]
  [answer? (any/c . -> . boolean?)]
  [pre-value? (any/c . -> . boolean?)]
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
;; Value := (value PreValue [Listof ContractClosure])
(struct value answer (pre refinements) #:transparent)
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
;; Cons := (cons/ Exp Exp)
(struct cons/ exp (car cdr) #:transparent)

;; Car := (car/ Exp)
(struct car/ exp (of) #:transparent)
;; Cdr := (cdr/ Exp)
(struct cdr/ exp (of) #:transparent)
;; Nil? := (nil?/ Exp)
(struct nil?/ exp (of) #:transparent)
;; Cons? := (cons?/ Exp)
(struct cons?/ exp (of) #:transparent)

;; Blame := (blame/ Label Label)
(struct blame/ answer (violator violatee) #:transparent)

;; PreValue := Opaque | Number | Boolean | Lambda
(define (pre-value? x)
  (or (number? x) (boolean? x) (opaque? x) (lam? x) (eq? 'nil x)))
;; Opaque := (opaque Type)
(struct opaque (type) #:transparent)
;; Lambda := (lambda Type Exp)
(struct lam (type body) #:transparent)
;; pre-value? : Any -> Boolean

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

;; ContractClosure = (contract-clo Contract [Env Value])
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
;; BaseType = 'Num | 'Bool | '⊥
(define (base-type? x)
  (member x '(Num Bool ⊥)))

;; TypeResult = Type | TypeError
(define (type-result? x)
  (or (type? x) (equal? x 'TypeError)))

;; δ : Op [Listof Value] -> [Setof Answer]
;; applies primitive op
(define (δ o xs)
  (if (andmap concrete? xs)
      {set (match (apply (op-impl o) (map value-pre xs))
             [(blame/ l1 l2) (blame/ l1 l2)]
             [u (value u ∅)])}
      (match (op-range o)
        ['Num {set (value (opaque 'Num) ∅)}]
        ['Bool {set (value #t ∅) (value #f ∅)}])))

;; concrete? : Value -> Boolean
;; checks whether value is concrete
(define concrete? (compose not opaque? value-pre))

;; check-real : (Real Real -> Bool) Symbol -> (Num Num -> Bool or Blame)
(define (check-real op name)
  (λ (x y)
    (if (and (real? x) (real? y))
        (op x y)
        (blame/ '† name))))

;; ops : Symbol → (List (Listof Type) Type Function)
;; primitive ops' types and implementations
(define ops
  (hash
   'zero? `((Num) Bool ,zero?)
   'non-neg? `((Num) Bool ,(and/c real? (compose not negative?)))
   'even? `((Num) Bool ,(and/c integer? even?))
   'odd? `((Num) Bool ,(and/c integer? odd?))
   'prime? `((Num) Bool ,(λ (n) (if (member n '(2 3 5 7 11 13) #t #f) #t #f)))
   'true? `((Bool) Bool ,(compose not false?))
   'false? `((Bool) Bool ,false?)
   'sqrt `((Num) Num ,sqrt)
   '+ `((Num Num) Num ,+)
   '- `((Num Num) Num ,-)
   '* `((Num Num) Num ,*)
   '= `((Num Num) Bool ,=)
   '≠ `((Num Num) Bool ,(compose not =))
   '< `((Num Num) Bool ,(check-real < '<))
   '≤ `((Num Num) Bool ,(check-real <= '≤))
   '> `((Num Num) Bool ,(check-real > '>))
   '≥ `((Num Num) Bool ,(check-real >= '≥))))

;; op-impl : Symbol -> Function
(define (op-impl name)
  (third (hash-ref ops name)))

;; op-range : Op -> ('Num or 'Bool)
;; returns op's return type
(define (op-range o)
  (second (hash-ref ops o)))

;; o1 : Symbol -> Boolean
(define (o1? name)
  (and (hash-has-key? ops name)
       (= 1 (length (first (hash-ref ops name))))))

;; o2 : Symbol -> Boolean
(define (o2? name)
  (and (hash-has-key? ops name)
       (= 2 (length (first (hash-ref ops name))))))

;; type-check : Exp -> TypeResult
(define (type-check e)
  
  ;; type-check-with : [Env TypeResult] Exp -> TypeResult
  (define (type-check-with tenv e)
    (match e
      [(ref d) (env-get-default d 'TypeError tenv)]
      [(value u cs) (match u
                      [(opaque t) t]
                      [(lam t b)
                       (extend func-type t
                               (type-check-with (env-extend t tenv) b))]
                      ['nil (list-type '⊥)]
                      [_ (cond
                           [(number? u) 'Num]
                           [(boolean? u) 'Bool])])]
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
                               (type-check-with tenv e))]
      [(cons/ e1 e2) (extend type-list
                             (type-check-with tenv e1)
                             (type-check-with tenv e2))]
      [(nil?/ e) (extend type-list→bool (type-check-with tenv e))]
      [(cons?/ e) (extend type-list→bool (type-check-with tenv e))]
      [(car/ e) (extend type-car (type-check-with tenv e))]
      [(cdr/ e) (extend type-cdr (type-check-with tenv e))]))
  
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
         [else 'TypeError])]))
  
  ;; extend : (Type* -> TypeResult) TypeResult* -> TypeResult
  ;; extends function's range from Type* to TypeResult*
  ;; returns 'TypeError if any argument is
  (define (extend f . maybeTypes)
    (if (ormap (curry equal? 'TypeError) maybeTypes)
        'TypeError
        (apply f maybeTypes)))
  
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
  
  ;; type-car : Type -> TypeResult
  (define (type-car t)
    (match t
      [(list-type te) te]
      [else 'TypeError]))
  
  ;; type-cdr : Type -> TypeResult
  (define (type-cdr t)
    (if (list-type? t) t 'TypeError))
  
  ;; type-list : Type Type -> TypeResult
  (define (type-list te tl)
    (match `(,te ,tl)
      [`(,t ,(list-type t1)) (if (⊑ t1 t) (list-type t) 'TypeError)]
      [else 'TypeError]))
  
  ;; type-list→bool : Type -> TypeResult
  (define (type-list→bool t)
    (if (list-type? t) 'Bool 'TypeError))
  
  ;; type-mon : Type Type -> TypeResult
  (define (type-mon c e)
    (match `(,c ,e)
      [`(,(con-type t1) ,t2) (if (equal? t1 t2) t1 'TypeError)]
      [else 'TypeError]))
  
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
    (let* ([entry (hash-ref ops o)]
           [param-types (first entry)])
      (if (andmap ⊑ arg-types param-types) (second entry) 'TypeError)))
  
  (type-check-with ρ0 e))

;; free-vars : Exp -> [Setof Natural]
(define (free-vars e)
  (vars≥ 0 e))
;; vars≥ : Exp -> [Setof Natural]
(define (vars≥ d e)
  (match e
    [(ref k) (if (>= k d) {set (- k d)} ∅)]
    [(value u cs) (match u
                    [(lam t b) (vars≥ (+ 1 d) b)]
                    [else ∅])]
    [(blame/ l1 l2) ∅]
    [(app e1 e2) (set-union (vars≥ d e1) (vars≥ d e2))]
    [(rec t b) (vars≥ (+ 1 d) b)]
    [(if/ e1 e2 e3) (set-union (vars≥ d e1) (vars≥ d e2) (vars≥ d e3))]
    [(prim-app o args) (apply set-union (map (curry vars≥ d) args))]
    [(mon h f g c e) (set-union (con-vars≥ d c) (vars≥ d e))]
    [(cons/ e1 e2) (set-union (vars≥ d e1) (vars≥ d e2))]
    [(nil?/ e) (vars≥ d e)]
    [(cons?/ e) (vars≥ d e)]
    [(car/ e) (vars≥ d e)]
    [(cdr/ e) (vars≥ d e)]))
;; con-free-vars : Contract -> [Setof Natural]
(define (con-free-vars c)
  (con-vars≥ 0 c))
;; con-vars≥ : Natural Contract -> [Setof Natural]
(define (con-vars≥ d c)
  (match c
    [(flat/c e) (vars≥ d e)]
    [(func/c c1 t c2) (set-union (con-vars≥ d c1) (con-vars≥ (+ 1 d) c2))]))

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
                               (value #f ∅))]
      [`(,t) (read-exp-with names t)]
      [`() (value #t ∅)]))
  
  ;; read-or : [Listof S-exp] -> Exp
  (define (read-or terms)
    (match terms
      [`(,t1 ,t2 ,ts ...) (if/ (read-exp-with names t1)
                               (value #t ∅)
                               (read-or (rest terms)))]
      [`(,t) (read-exp-with names t)]
      [`() (value #f ∅)]))
  
  (match s
    [`(• ,t) (value (opaque (read-type t)) ∅)]
    [`(λ (,x ,t) ,s) (if (symbol? x)
                         (value (lam (read-type t)
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
    [`(cons ,s1 ,s2) (cons/ (read-exp-with names s1)
                            (read-exp-with names s2))]
    [`(nil? ,s) (nil?/ (read-exp-with names s))]
    [`(cons? ,s) (cons?/ (read-exp-with names s))]
    [`(car ,s) (car/ (read-exp-with names s))]
    [`(cdr ,s) (cdr/ (read-exp-with names s))]
    [`(and ,terms ...) (read-and terms)]
    [`(or ,terms ...) (read-or terms)]
    [`(,s0 ,s1)
     (if (o1? s0)
         (prim-app s0 (list (read-exp-with names s1)))
         (app (read-exp-with names s0) (read-exp-with names s1)))]
    [`(,s0 ,s1 ,s2)
     (if (o2? s0)
         (prim-app s0 (list (read-exp-with names s1) (read-exp-with names s2)))
         (error "expect binary op, given: " s0))]
    [x (cond
         [(pre-value? x) (value x ∅)]
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
      [(value u _)
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
                             ,(show-exp-with names e))]
      [(cons/ e1 e2) `(cons ,(show-exp-with names e1)
                            ,(show-exp-with names e2))]
      [(nil?/ e) `(nil? ,(show-exp-with names e))]
      [(cons?/ e) `(cons? ,(show-exp-with names e))]
      [(car/ e) `(car ,(show-exp-with names e))]
      [(cdr/ e) `(cdr ,(show-exp-with names e))]))
  
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