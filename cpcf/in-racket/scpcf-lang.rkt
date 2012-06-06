#lang racket
(require redex) ; variable-not-in
(require rackunit)
(require racket/contract)

(require "env.rkt")

(provide
 
 (contract-out
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
  [struct ref ([distance natural?])]
  [struct mon-lam ([orig label?] [pos label?] [neg label?]
                                 [con func/c?] [con-env env?]
                                 [lam pre-value? #|can be opaque|#])]
  
  [struct flat/c ([exp exp?])]
  [struct func/c ([dom contract/?] [type type?] [rng contract/?])]
  
  ;; hiding constructors 'clo' and 'contract-clo' would make it tedious
  ;; due to lack of pattern matching. But client is expected to use
  ;; 'close' instead of 'clo', and 'close-contract' instead of 'contract-clo'
  [struct clo ([exp exp?] [env env?])]
  [close (exp? env? . -> . clo?)]
  [struct contract-clo ([con contract/?] [env env?])]
  [close-contract (contract/? env? . -> . contract-clo?)]
  
  ;; Type := BaseType | FuncType | ConType
  ;; BaseType = 'Num | 'Bool | '⊥
  [struct func-type ([from type?] [to type?])]
  [struct con-type ([of type?])]
  
  [δ (op? (listof value?) . -> . (set/c answer?))]
  
  [type-check (exp? . -> . type-result?)]
  
  [read-exp (s-exp? . -> . exp?)]
  [show-exp (exp? . -> . s-exp?)]
  [show-type (type-result? . -> . s-exp?)]
  
  [exp? (any/c . -> . boolean?)]
  [answer? (any/c . -> . boolean?)]
  ;; PreValue := Opaque | Number | Boolean | Lambda
  [pre-value? (any/c . -> . boolean?)]
  [label? (any/c . -> . boolean?)]
  [op? (any/c . -> . boolean?)]
  [o1? (any/c . -> . boolean?)]
  [o2? (any/c . -> . boolean?)]
  [type? (any/c . -> . boolean?)]
  [base-type? (any/c . -> . boolean?)]
  [type-result? (any/c . -> . boolean?)]
  [s-exp? (any/c . -> . boolean?)])
 
 ∅ ;; empty set
 
 ;; example terms
 ev? db1 db2 ap0 ap1 ap00 ap01 ap10 tri
 keygen rsa rsa-ap ;sqroot sqrt-user sqrt-ap
 
 ;; example contracts
 c/any c/prime c/non-neg
 )

;; s-exp? : Any -> Boolean
(define s-exp? any/c) ; TODO

(struct exp () #:transparent)
(struct answer exp () #:transparent)
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

;; Value := (value PreValue [Listof ContractClosure])
(struct value answer (pre refinements) #:transparent)

;; Opaque := (opaque Type)
(struct opaque (type) #:transparent)
;; Lambda := (lambda Type Exp)
(struct lam (type body) #:transparent)
;; pre-value? : Any -> Boolean
(define (pre-value? x)
  (or (number? x) (boolean? x) (opaque? x) (lam? x) (mon-lam? x)))

;; MonitoredLambda := (mon-lam Label Label Label FuncContract [Env Value] Exp)
;; monitored lambda, for internal use only
;; con-env is the environment that closes the monitoring contract, which is
;; of the form (C1 ↦ λ.C2)
(struct mon-lam (orig pos neg con con-env lam) #:transparent)

;; Blame := (blame/ Label Label)
(struct blame/ answer (violator violatee) #:transparent)

;; Ref := (ref Natural)
(struct ref exp (distance) #:transparent)

;; Op := O1 | O2
(define (op? o)
  (or (o1? o) (o2? o)))
(define (o1? o)
  (member o '(zero? non-neg? even? odd? prime? true? false? sqrt)))
(define (o2? o)
  (member o '(+ - ∨ ∧)))

;; label? : Any -> Boolean
(define label? symbol?)

;; Contract := FlatContract | FuncContract
(struct contract/ () #:transparent)
(struct flat/c contract/ (exp) #:transparent)
(struct func/c contract/ (dom type rng) #:transparent)

;; Closure := (clo Exp [Env Value])
(struct clo (exp env) #:transparent)

;; close : Exp Env -> Closure
(define (close exp en)
  (clo exp (env-restrict (free-vars exp) en)))

;; ContractClosure = (contract-clo Contract [Env Value])
(struct contract-clo (con env) #:transparent)

;; close-contract : Contract Env -> ContractClosure
(define (close-contract con en)
  (contract-clo con (env-restrict (con-free-vars con) en)))

;; type? : Any -> Boolean
;; Type = BaseType | (func-type Type Type) | (con-type Type)
(define (type? x)
  (or (base-type? x) (func-type? x) (con-type? x)))

(struct func-type (from to) #:transparent)
(struct con-type (of) #:transparent)

;; base-type? : Any -> Boolean
;; BaseType = 'Num | 'Bool | '⊥
(define (base-type? x)
  (member x '(Num Bool ⊥)))

;; TypeResult = Type | TypeError
(define (type-result? x)
  (or (type? x) (equal? x 'TypeError)))

;; ∅ : Set
(define ∅ (set))

;; δ : Op [Listof Value] -> [Setof Answer]
;; applies primitive op
(define (δ o xs)
  (if (andmap concrete? xs)
      {set (value (apply (op-impl o) (map value-pre xs)) ∅)}
      (match (op-range o)
        ['Num {set (value (opaque 'Num) ∅)}]
        ['Bool {set (value #t ∅) (value #f ∅)}])))

;; concrete? : Value -> Boolean
;; checks whether value is concrete
(define concrete? (compose not opaque? value-pre))

;; op-impl : Op -> PrimitiveOp
;; given op-name in object language, return its implementation
(define (op-impl o)
  (match o
    ['zero? zero?]
    ['non-neg? (and/c real? (compose not negative?))]
    ['even? (and/c integer? even?)]
    ['odd? (and/c integer? odd?)]
    ['prime? (λ (n) (if (member n '(2 3 5 7 11 13)) #t #f))] ; force #t
    ['true? (compose not false?)]
    ['false? false?]
    ['sqrt sqrt]
    ['+ +]
    ['- -]
    ['∨ (λ (x y) (or x y))]
    ['∧ (λ (x y) (and x y))]))

;; op-range : Op -> ('Num or 'Bool)
;; returns op's return type
(define (op-range o)
  (if (member o '(sqrt + -)) 'Num 'Bool))

;; type-check : Exp -> TypeResult
(define (type-check e)
  
  ;; type-check-with : [Env TypeResult] Exp -> TypeResult
  (define (type-check-with tenv e)
    (match e
      [(ref d) (env-get-default d 'TypeError tenv)]
      [(value (opaque t) refinements) t]
      [(value (lam type body) refinements)
       (extend func-type type (type-check-with (env-extend type tenv) body))]
      [(blame/ l1 l2) '⊥]
      [(app f x) (extend type-app
                         (type-check-with tenv f)
                         (type-check-with tenv x))]
      [(rec type body) (type-check-with 
                        (env-extend type tenv) body)]
      [(if/ e1 e2 e3) (extend type-if
                              (type-check-with tenv e1)
                              (type-check-with tenv e2)
                              (type-check-with tenv e3))]
      [(prim-app o args) (apply (curry extend (∆ o)) (map (curry type-check-with tenv) args))]
      [(mon h f g c e)
       (extend type-mon
               (type-check-con-with tenv c)
               (type-check-with tenv e))]
      [(value u refinements)
       (cond
         [(number? u) 'Num]
         [(boolean? u) 'Bool])]))
  
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
      [(func-type dom rng) (if (equal? arg dom) rng 'TypeError)]
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
  
  ;; Type Type -> TypeResult
  ;; returns most specific supertype
  (define (⊔ t1 t2)
    (match `(,t1 ,t2)
      [`(,t ,t) t]
      [`(⊥ ,t) t]
      [`(,t ⊥) t]
      [`(,(func-type x y1) ,(func-type x y2)) (func-type x (⊔ y1 y2))]
      [`(,(con-type t1) ,(con-type t2)) (con-type (⊔ t1 t2))]
      [else 'TypeError]))
  
  ;; ∆ : Op -> ((Type -> TypeResult) or (Type Type -> TypeResult))
  (define (∆ o)
    (cond
      [(member o '(zero? non-neg? even? odd? prime?))
       (λ (t) (match t ['Num 'Bool] [else 'TypeError]))]
      [(member o '(true? false?))
       (λ (t) (match t ['Bool 'Bool] [else 'TypeError]))]
      [(equal? o 'sqrt)
       (λ (t) (match t ['Num 'Num] [else 'TypeError]))]
      [(member o '(+ -))
       (λ (t1 t2) (match `(,t1 ,t2) ['(Num Num) 'Num] [else 'TypeError]))]
      [(member o '(∨ ∧))
       (λ (t1 t2) (match `(,t1 ,t2) ['(Bool Bool) 'Bool] [else 'TypeError]))]))
  
  (type-check-with env-empty e))

;; free-vars : Exp -> [Setof Natural]
(define (free-vars e)
  (vars≥ 0 e))
;; vars≥ : Exp -> [Setof Natural]
(define (vars≥ d e)
  (match e
    [(value u cs) (match u
                    [(lam t b) (vars≥ (+ 1 d) b)]
                    [else ∅])]
    [(blame/ l1 l2) ∅]
    [(app e1 e2) (set-union (vars≥ d e1) (vars≥ d e2))]
    [(rec t b) (vars≥ (+ 1 d) b)]
    [(if/ e1 e2 e3) (set-union (vars≥ d e1) (vars≥ d e2) (vars≥ d e3))]
    [(prim-app o args) (apply set-union (map (curry vars≥ d) args))]
    [(mon h f g c e) (set-union (con-vars≥ d c) (vars≥ d e))]
    [(mon-lam h f g c ρc e) (vars≥ d e)]
    [(ref k) (if (>= k d) {set k} ∅)]))
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
    [else (error "invalid contract form: " s)]))

;; read-exp-with : [Listof Symbol] S-exp -> Exp
(define (read-exp-with names s)
  
  ;; name-distance : Symbol [Listof Symbol] -> Natural
  (define (name-distance x xs)
    ;; go : Natural [Listof Symbol] -> Natural
    (define (go pos xs)
      (match xs
        [(cons z zs) (if (equal? z x) pos (go (+ 1 pos) zs))]
        [empty (error "expression not closed, unbound variable: " x )]))
    (go 0 xs))
  
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
    [`(,s0 ,s1)
     (if (o1? s0)
         (prim-app s0 (list (read-exp-with names s1)))
         {app (read-exp-with names s0) (read-exp-with names s1)})]
    [`(,s0 ,s1 ,s2)
     (if (o2? s0)
         (prim-app s0 (list (read-exp-with names s1) (read-exp-with names s2)))
         (error "expect binary op, given: " s0))]
    [x (cond
         [(or (boolean? x) (number? x)) (value x ∅)]
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
      [(value (opaque t) _) `(• ,(show-type t))]
      [(value (lam t b) _)
       (let ([x ((if (func-type? t) new-fun-name new-var-name) names)])
         `(λ (,x ,(show-type t))
            ,(show-exp-with (cons x names) b)))]
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
      [(value u refinements) u]
      ;; closed expressions can't cause error
      [(ref d) (list-ref names d)]))
  
  ;; show-con-with : [Listof Symbol] Contract -> S-exp
  (define (show-con-with names c)
    (match c
      [(flat/c e) `(flat ,(show-exp-with names e))]
      [(func/c c t d)
       `(,(show-con-with names c)
         ↦
         ,(let ([x (new-var-name names)])
            `(λ (,x ,(show-type t)) ,(show-con-with (cons x names) d))))]))
  
  (show-exp-with empty e))

;; show-type : TypeResult -> S-exp
(define (show-type t)
  (match t
    [(func-type dom rng) `(,(show-type dom) → ,(show-type rng))]
    [(con-type t) `(con ,(show-type t))]
    [t t]))

;; example terms

; contracts
(define c/any `(flat (λ (x Num) #t)))
(define c/prime `(flat (λ (x Num) (prime? x))))
(define c/non-neg `(flat (λ (x Num) (non-neg? x))))

; expressions
(define ev? '(λ (x Num) (even? x)))
(define db1
  `(mon h f g
        (((flat ,ev?) ↦ (flat ,ev?))
         ↦ ((flat ,ev?) ↦ (flat ,ev?)))
        (λ (f (Num → Num))
          (λ (x Num)
            (f (f x))))))
(define db2 ; like db1, but wrong
  `(mon h f g
        (((flat ,ev?) ↦ (flat ,ev?))
         ↦ ((flat ,ev?) ↦ (flat ,ev?)))
        (λ (f (Num → Num))
          (λ (x Num) 7))))
(define ap0
  `(,db1 (λ (x Num) 2)))
(define ap1
  `(,db1 (λ (x Num) 7)))
(define ap00 `(,ap0 42))
(define ap01 `(,ap0 13))
(define ap10 `(,ap1 0))
(define tri `(μ (f (Num → Num))
                (λ (n Num)
                  (if (zero? n) 0
                      (+ n (f (- n 1)))))))
(define ap00-db2 `((,db2 ,ap0) 0))
(define keygen ; opaque
  `(mon h f g (,c/any ↦ ,c/prime) (• (Num → Num))))
(define rsa ; opaque
  `(mon h f g (,c/prime ↦ (,c/any ↦ ,c/any)) (• (Num → (Num → Num)))))
(define rsa-ap
  `((,rsa (,keygen 13)) (• Num)))
#;(define sqroot
  `(mon h f g (,c/non-neg ↦ ,c/non-neg)
        (λ (x Num) (sqrt x))))
#;(define sqrt-user
  `(mon h f g ((,c/any ↦ ,c/any) ↦ ,c/any)
        (λ (f (Num → Num)) (,sqroot (f 0)))))
#;(define sqrt-ap
  `(,sqrt-user (• (Num → Num))))

;;;;; testing
(define exps (list ev? db1 db2 ap0 ap1 ap00 ap01 ap10 tri ap00-db2))

;; test read/show
(for-each (λ (e)
            (check-equal?
             (read-exp e)
             ((compose read-exp show-exp read-exp) e)))
          exps)
;; test type-checking
(define tc (compose show-type type-check read-exp))
(check-equal? (tc ev?) '(Num → Bool))
(check-equal? (tc db1) '((Num → Num) → (Num → Num)))
(check-equal? (tc ap0) '(Num → Num))
(check-equal? (tc ap00) 'Num)
(check-equal? (tc tri) '(Num → Num))
(check-equal? (tc keygen) '(Num → Num))
(check-equal? (tc rsa) '(Num → (Num → Num)))
(check-equal? (tc rsa-ap) 'Num)
#;(check-equal? (tc sqroot) '(Num → Num))
#;(check-equal? (tc sqrt-user) '((Num → Num) → Num))
#;(check-equal? (tc sqrt-ap) 'Num)