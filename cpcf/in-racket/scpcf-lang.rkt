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
  
  [struct flat/c ([exp exp?])]
  [struct func/c ([dom contract/?] [type type?] [rng contract/?])]
  
  [struct contract-clo ([con contract/?] [env env?])]
  
  
  ;; Type := BaseType | FuncType | ConType
  ;; BaseType = 'Int | 'Bool | '⊥
  [struct func-type ([from type?] [to type?])]
  [struct con-type ([of type?])]
  
  [δ (op? (listof value?) . -> . (set/c answer?))]
  
  [type-check (exp? . -> . type-result?)]
  
  [read-exp (s-exp? . -> . exp?)]
  [show-exp (exp? . -> . s-exp?)]
  [show-type (type? . -> . s-exp?)]
  
  [exp? (any/c . -> . boolean?)]
  [answer? (any/c . -> . boolean?)]
  ;; PreValue := Opaque | Integer | Boolean | Lambda
  [pre-value? (any/c . -> . boolean?)]
  [var? (any/c . -> . boolean?)]
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
 keygen rsa rsa-ap sqroot sqrt-user sqrt-ap
 
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
  (or (integer? x) (boolean? x) (opaque? x) (lam? x)))

;; Blame := (blame/ Label Label)
(struct blame/ answer (violator violatee) #:transparent)

;; var? : Any -> Boolean
(define (var? x)
  (and (integer? x) (>= x 0)))

;; Op := O1 | O2
(define (op? o)
  (or (o1? o) (o2? o)))
(define (o1? o)
  (member o '(zero? non-neg? even? odd? prime? true? false? sqrt)))
(define (o2? o)
  (member o '(+ -)))

;; label? : Any -> Boolean
(define label? symbol?)

(struct contract/ () #:transparent)
(struct flat/c contract/ (exp) #:transparent)
(struct func/c contract/ (dom type rng) #:transparent)

;; ContractClosure = (contract-clo Contract [Env Value])
(struct contract-clo (con env) #:transparent)

;; type? : Any -> Boolean
;; Type = BaseType | (func-type Type Type) | (con-type Type)
(define (type? x)
  (or (base-type? x) (func-type? x) (con-type? x)))

(struct func-type (from to) #:transparent)
(struct con-type (of) #:transparent)

;; base-type? : Any -> Boolean
;; BaseType = 'Int | 'Bool | '⊥
(define (base-type? x)
  (member x '(Int Bool ⊥)))

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
        ['Int 
         (match o
           ['sqrt {set (value (opaque 'Int)
                              {set (contract-clo (read-con c/non-neg) env-empty)})}]
           [else {set (value (opaque 'Int) ∅)}])]
        ['Bool {set (value #t ∅) (value #f ∅)}])))

;; concrete? : Value -> Boolean
;; checks whether value is concrete
(define concrete? (compose not opaque? value-pre))

;; op-impl : Op -> PrimitiveOp
;; given op-name in object language, return its implementation
(define (op-impl o)
  (match o
    ['zero? zero?]
    ['non-neg? (compose not negative?)]
    ['even? even?]
    ['odd? odd?]
    ['prime? (λ (n) (if (member n '(2 3 5 7 11 13)) #t #f))] ; force #t
    ['true? (compose not false?)]
    ['false? false?]
    ['sqrt (compose inexact->exact floor sqrt)]
    ['+ +]
    ['- -]))

;; op-range : Op -> ('Int or 'Bool)
;; returns op's return type
(define (op-range o)
  (if (member o '(sqrt + -)) 'Int 'Bool))

;; type-check : Exp -> TypeResult
(define (type-check e)
  
  ;; type-check-with : [Env TypeResult] Exp -> TypeResult
  (define (type-check-with tenv e)
    (match e
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
         [(integer? u) 'Int]
         [(boolean? u) 'Bool])]
      [var (env-get-default var 'TypeError tenv)]))
  
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
       (λ (t) (match t ['Int 'Bool] [else 'TypeError]))]
      [(member o '(true? false?))
       (λ (t) (match t ['Bool 'Bool] [else 'TypeError]))]
      [(equal? o 'sqrt)
       (λ (t) (match t ['Int 'Int] [else 'TypeError]))]
      [(member o '(+ -))
       (λ (t1 t2) (match `(,t1 ,t2) ['(Int Int) 'Int] [else 'TypeError]))]))
  
  (type-check-with env-empty e))

;; read-exp : S-exp -> Exp
(define (read-exp s)
  (read-exp-with empty s))

;; read-con : S-exp -> Contract
(define (read-con s)
  (read-con-with empty s))

;; read-type : S-exp -> Type
(define (read-type s)
  (match s
    ['Int 'Int]
    ['Bool 'Bool]
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
       (read-con-with names `(,c ↦ (λ (,x Int) ,d))))]
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
         [(or (boolean? x) (integer? x)) (value x ∅)]
         [(symbol? x) (name-distance x names)]
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
      [distance (list-ref names distance)]))
  
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

;; show-type : Type -> S-exp
(define (show-type t)
  (match t
    [(func-type dom rng) `(,(show-type dom) → ,(show-type rng))]
    [(con-type t) `(con ,(show-type t))]
    [t t]))

;; example terms

; contracts
(define c/any `(flat (λ (x Int) #t)))
(define c/prime `(flat (λ (x Int) (prime? x))))
(define c/non-neg `(flat (λ (x Int) (non-neg? x))))

; expressions
(define ev? '(λ (x Int) (even? x)))
(define db1
  `(mon h f g
        (((flat ,ev?) ↦ (flat ,ev?))
         ↦ ((flat ,ev?) ↦ (flat ,ev?)))
        (λ (f (Int → Int))
          (λ (x Int)
            (f (f x))))))
(define db2 ; like db1, but wrong
  `(mon h f g
        (((flat ,ev?) ↦ (flat ,ev?))
         ↦ ((flat ,ev?) ↦ (flat ,ev?)))
        (λ (f (Int → Int))
          (λ (x Int) 7))))
(define ap0
  `(,db1 (λ (x Int) 2)))
(define ap1
  `(,db1 (λ (x Int) 7)))
(define ap00 `(,ap0 42))
(define ap01 `(,ap0 13))
(define ap10 `(,ap1 0))
(define tri `(μ (f (Int → Int))
                (λ (n Int)
                  (if (zero? n) 0
                      (+ n (f (- n 1)))))))
(define ap00-db2 `((,db2 ,ap0) 0))
(define keygen ; opaque
  `(mon h f g (,c/any ↦ ,c/prime) (• (Int → Int))))
(define rsa ; opaque
  `(mon h f g (,c/prime ↦ (,c/any ↦ ,c/any)) (• (Int → (Int → Int)))))
(define rsa-ap
  `((,rsa (,keygen 13)) (• Int)))
(define sqroot
  `(mon h f g (,c/non-neg ↦ ,c/non-neg)
        (λ (x Int) (sqrt x))))
(define sqrt-user
  `(mon h f g ((,c/any ↦ ,c/any) ↦ ,c/any)
        (λ (f (Int → Int)) (,sqroot (f 0)))))
(define sqrt-ap
  `(,sqrt-user (• (Int → Int))))

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
(check-equal? (tc ev?) '(Int → Bool))
(check-equal? (tc db1) '((Int → Int) → (Int → Int)))
(check-equal? (tc ap0) '(Int → Int))
(check-equal? (tc ap00) 'Int)
(check-equal? (tc tri) '(Int → Int))
(check-equal? (tc keygen) '(Int → Int))
(check-equal? (tc rsa) '(Int → (Int → Int)))
(check-equal? (tc rsa-ap) 'Int)
(check-equal? (tc sqroot) '(Int → Int))
(check-equal? (tc sqrt-user) '((Int → Int) → Int))
(check-equal? (tc sqrt-ap) 'Int)