#lang racket
(require redex) ; variable-not-in
(require rackunit)

;; Exp = Answer | Var | App | Rec | If | PrimApp | Mon

;; Answer = Value | Blame

(struct value (pre refinements))
;; Value = (value PreValue (Listof Contract))

;; PreValue = Opaque | Integer | Boolean | Lambda

(struct opaque (type))
;; Opaque = (opaque Type)

(struct lam (var type body))
;; Lambda = (lam Var Type Exp)

;; Var = Symbol
(define var? symbol?)

(struct app (func arg))
;; App = (app Exp Exp)

(struct rec (name type body))
;; Rec = (rec Var Type Exp)

(struct if/ (test then else))
;; If = (if/ Exp Exp Exp)

(struct prim-app (op args))
;; PrimApp = (prim-app Op (Listof Exp))

;; Op = O1 | O2
(define (op? o)
  (or (o1? o) (o2? o)))

;; O1 = zero? | non-neg? | even? | odd? | prime? | true? | false? | sqrt
(define (o1? o)
  (member o '(zero? non-neg? even? odd? prime? true? false? sqrt)))

;; O2 = + | -
(define (o2? o)
  (member o '(+ -)))

(struct mon (origin pos neg con exp))
;; Mon = (mon Label Label Label Contract Exp)

;; Label = Symbol
(define label? symbol?)

(struct blame (violator violatee))
;; Blame = (blame Label Label)

;; Contract = (flat/c Exp) | (func/c Contract Var Type Contract)
(struct flat/c (exp))
(struct func/c (dom var type rng))

;; Type = BaseType | (func-type Type Type) | (con-type Type)
(struct func-type (from to))
(struct con-type (of))
;; BaseType = 'Int | 'Bool | '⊥

;; TypeResult = Type | TypeError

;; δ : Op (Listof Value) -> (Listof Answer)
;; applies primitive op
(define (δ o xs)
  (if (andmap concrete? xs)
      (list (value (apply (op-impl o) (map value-pre xs)) empty))
      (match (op-range o)
        ['Int (list (opaque 'Int))]
        ['Bool `((#t ()) (#f ()))])))

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
    ['prime? (λ (n) (member n '(2 3 5 7 11 13)))]
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
  
  ;; type-check-with : [Listof (list Var Type)] Exp -> TypeResult
  (define (type-check-with tenv e)
    (match e
      [(value (opaque t) refinements) t]
      [(value (lam var type body) refinements)
       (lift func-type type (type-check-with (cons `(,var ,type) tenv) body))]
      [(blame l1 l2) '⊥]
      [(app f x) (lift type-app
                       (type-check-with tenv f)
                       (type-check-with tenv x))]
      [(rec var type body) (type-check-with 
                            (cons `(,var ,type) tenv) body)]
      [(if/ e1 e2 e3) (lift type-if
                            (type-check-with tenv e1)
                            (type-check-with tenv e2)
                            (type-check-with tenv e3))]
      [(prim-app o args) (apply (curry lift (∆ o)) (map (curry type-check-with tenv) args))]
      [(mon h f g con e)
       (lift type-mon
             (type-check-con-with tenv con)
             (type-check-with tenv e))]
      [(value u refinements)
       (cond
         [(integer? u) 'Int]
         [(boolean? u) 'Bool])]
      [else 
       (if (var? e) (or (second (assoc e tenv)) 'TypeError) 'TypeError)]))
  
  ;; type-check-con-with : [Listof (list Var Type)] Contract -> TypeResult
  (define (type-check-con-with tenv c)
    (match c
      [(flat/c e) (match (type-check-with tenv e)
                    [(func-type t 'Bool) (lift con-type t)]
                    [else 'TypeError])]
      [(func/c dom x t rng)
       (match `(,(type-check-con-with tenv dom)
                ,(type-check-con-with (cons `(,x ,t) tenv) rng))
         [`(,(con-type t1) ,(con-type t2))
          (lift con-type (func-type t1 t2))]
         [else 'TypeError])]))
  
  ;; lift : (Type* -> TypeResult) TypeResult* -> TypeResult
  (define (lift f . maybeTypes)
    (if (ormap (curry equal? 'TypeError) maybeTypes)
        'TypeError
        (apply f maybeTypes)))
  
  ;; type-app : Type Type -> TypeResult
  (define (type-app f arg)
    (match f
      [(func-type dom rng) (if (type=? arg dom) rng 'TypeError)]
      [else 'TypeError]))
  
  ;; type-if : Type Type Type -> TypeResult
  (define (type-if t1 t2 t3)
    (match t1
      ['Bool (⊔ t2 t3)]
      [else 'TypeError]))
  
  ;; type=? : Type Type -> Boolean
  (define (type=? t1 t2)
    (match `(,t1 ,t2)
      [`(,(func-type x1 y1) ,(func-type x2 y2))
       (and (type=? x1 x2) (type=? x2 y2))]
      [`(,(con-type x1) ,(con-type x2)) (type=? x1 x2)]
      [else (equal? t1 t2)]))
  
  ;; type-mon : Type Type -> TypeResult
  (define (type-mon c e)
    (match `(,c ,e)
      [`(,(con-type t1) ,t2) (if (type=? t1 t2) t1 'TypeError)]
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
  
  (type-check-with empty e))

;; read-exp : S-exp -> Exp
(define (read-exp s)
  (match s
    [`(• ,t) (value (opaque (read-type t)) empty)]
    [`(λ (,x ,t) ,e) (if (symbol? x)
                         (value (lam x (read-type t) (read-exp e)) empty)
                         (error "λ: expect symbol, given: " x))]
    [`(blame ,f ,g) (if (and (symbol? f) (symbol? g))
                        (blame f g)
                        (error "blame: expect symbols, given: " f g))]
    [`(μ (,f ,t) ,e) (if (symbol? f)
                         (rec f (read-type t) (read-exp e))
                         (error "μ: expect symbol, given: " f))]
    [`(if ,e1 ,e2 ,e3) (if/ (read-exp e1) (read-exp e2) (read-exp e3))]
    [`(mon ,h ,f ,g ,c ,e)
     (if (andmap symbol? `(,h ,f ,g))
         (mon h f g (read-con c) (read-exp e))
         (error "mon: expect symbols, given: " h f g))]
    [`(,e0 ,e1)
     (if (o1? e0)
         (prim-app e0 (list (read-exp e1)))
         (app (read-exp e0) (read-exp e1)))]
    (`(,o2 ,e1 ,e2)
     (if (o2? o2)
         (prim-app o2 (list (read-exp e1) (read-exp e2)))
         (error "expect primitive binary op, given: " o2)))
    (x (cond
         [(integer? x) (value x empty)]
         [(boolean? x) (value x empty)]
         [(var? x) x]
         [else (error "invalid expression form: " x)]))))

;; read-type : S-exp -> Type
(define (read-type s)
  (match s
    ['Int 'Int]
    ['Bool 'Bool]
    [`(,t1 → ,t2) (func-type (read-type t1) (read-type t2))]
    [`(con ,t) (con-type (read-type t))]
    [else (error "invalid type form: " s)]))

;; read-con : S-exp -> Contract
(define (read-con s)
  (match s
    [`(flat ,e) (flat/c (read-exp e))]
    [`(,c ↦ (λ (,x ,t) ,d))
     (if (symbol? x)
         (func/c (read-con c) x (read-type t) (read-con d))
         (error "function contract: expect symbol, given: " x))]
    [`(,c ↦ ,d)
     (let ([x (variable-not-in d 'dummy)])
       (func/c (read-con c) x 'Int (read-con d)))]
    [else (error "invalid contract form: " s)]))

;; show-exp : Exp -> S-exp
(define (show-exp e)
  (match e
    [(value (opaque t) _) `(• ,t)]
    [(value (lam var type body) _)
     `(λ (,var ,(show-type type)) ,(show-exp body))]
    [(blame l1 l2) `(blame ,l1 ,l2)]
    [(app f x) (map show-exp `(,f ,x))]
    [(rec var type body) `(μ (,var ,(show-type type)) ,(show-exp body))]
    [(if/ e1 e2 e3) `(if ,@(map show-exp `(e1 e2 e3)))]
    [(prim-app o args) `(,o ,@(map show-exp args))]
    [(mon h f g con e) `(mon ,h ,f ,g ,(show-con con) ,(show-exp e))]
    [(value u refinements) u]
    [x x]))

;; show-type : Type -> S-exp
(define (show-type t)
  (match t
    [(func-type dom rng) `(,(show-type dom) → ,(show-type rng))]
    [(con-type t) `(con ,(show-type t))]
    [t t]))

;; show-con : Contract -> S-exp
(define (show-con c)
  (match c
    [(flat/c e) `(flat ,(show-exp e))]
    [(func/c dom var type rng)
     `(,(show-con dom) ↦ (λ (,var ,(show-type type)) ,(show-con rng)))]))

;; example terms
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

;;;;; testing
(define exps (list ev? db1 db2 ap0 ap1 ap00 ap01 ap10 tri ap00-db2))

;; test read/show
(define show-back (compose show-exp read-exp))
(for-each (λ (e)
            (check-equal?
             ; just 'e' doesn't work due to syntax desugaring
             (show-back e)
             ((compose show-back show-back) e)))
          exps)
;; test type-checking
(define tc (compose show-type type-check read-exp))
(check-equal? (tc ev?) '(Int → Bool))
(check-equal? (tc db1) '((Int → Int) → (Int → Int)))
(check-equal? (tc ap0) '(Int → Int))
(check-equal? (tc ap00) 'Int)
(check-equal? (tc tri) '(Int → Int))