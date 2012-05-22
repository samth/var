#lang racket
(require redex) ; variable-not-in
(require rackunit)
(require racket/contract)

(provide
 
 (contract-out
  [struct value ([pre pre-value?] [refinements (listof contract/?)])]
  [struct opaque ([type type?])]
  
  [struct lam ([var var?] [type type?] [body exp?])]
  [struct app ([func exp?] [arg exp?])]
  [struct rec ([name var?] [type type?] [body exp?])]
  [struct if/ ([test exp?] [then exp?] [else exp?])]
  [struct mon ([orig label?] [pos label?] [neg label?]
                             [con contract/?] [exp exp?])]
  [struct prim-app ([op op?] [args (listof exp?)])]
  [struct blame/ ([violator label?] [violatee label?])]
  
  [struct flat/c ([exp exp?])]
  [struct func/c ([dom contract/?] [var var?] [type type?] [rng contract/?])]
  
  
  ;; Type := BaseType | FuncType | ConType
  ;; BaseType = 'Int | 'Bool | '⊥
  [struct func-type ([from type?] [to type?])]
  [struct con-type ([of type?])]
  
  [δ (op? (listof value?) . -> . (listof answer?))]
  
  [subst (var? exp? exp? . -> . exp?)]
  [subst-con (var? exp? contract/? . -> . contract/?)]
  
  [type-check (exp? . -> . type-result?)]
  
  [read-exp (s-exp? . -> . exp?)]
  [show-exp (exp? . -> . s-exp?)]
  [show-type (type? . -> . s-exp?)]
  [show-con (contract/? . -> . s-exp?)]
  
  [exp=? (exp? exp? . -> . boolean?)]
  [con=? (contract/? contract/? . -> . boolean?)]
  
  ;; Exp := Answer | Var | App | Rec | If | PrimApp | Mon
  [exp? (any/c . -> . boolean?)]
  ;; Answer := Value | Blame
  [answer? (any/c . -> . boolean?)]
  ;; PreValue := Opaque | Integer | Boolean | Lambda
  [pre-value? (any/c . -> . boolean?)]
  [var? (any/c . -> . boolean?)]
  [label? (any/c . -> . boolean?)]
  [op? (any/c . -> . boolean?)]
  [o1? (any/c . -> . boolean?)]
  [o2? (any/c . -> . boolean?)]
  [contract/? (any/c . -> . boolean?)]
  [type? (any/c . -> . boolean?)]
  [base-type? (any/c . -> . boolean?)]
  [type-result? (any/c . -> . boolean?)]
  [s-exp? (any/c . -> . boolean?)])
 
 ;; example terms
 ev? db1 db2 ap0 ap1 ap00 ap01 ap10 tri
 keygen rsa rsa-ap sqroot sqrt-user sqrt-ap
 
 ;; example contracts
 c/any c/prime c/non-neg
 )

;; s-exp? : Any -> Boolean
(define s-exp? any/c) ; TODO

;; answer : Any -> Boolean
(define (answer? x)
  (or (value? x) (blame/? x)))

;; Value := (value PreValue [Listof Contract])
(struct value (pre refinements))

;; pre-value? : Any -> Boolean
(define (pre-value? x)
  (or (integer? x) (boolean? x) (opaque? x) (lam? x)))

;; Opaque := (opaque Type)
(struct opaque (type))

;; Lambda := (lambda Var Type Exp)
(struct lam (var type body))

;; var? : Any -> Boolean
(define var? symbol?)

;; App := (app Exp Exp)
(struct app (func arg))

;; Rec := (rec Var Type Exp)
(struct rec (name type body))

;; If := (if/ Exp Exp Exp)
(struct if/ (test then else))

;; PrimApp := (prim-app Op [Listof Exp])
(struct prim-app (op args))

;; Op := O1 | O2
(define (op? o)
  (or (o1? o) (o2? o)))
(define (o1? o)
  (member o '(zero? non-neg? even? odd? prime? true? false? sqrt)))
(define (o2? o)
  (member o '(+ -)))

;; Mon := (mon Label Label label Contract Exp)
(struct mon (orig pos neg con exp))

;; label? : Any -> Boolean
(define label? symbol?)

;; blame/ := (blame/ Label Label)
(struct blame/ (violator violatee))

;; exp : Any -> Boolean?
(define (exp? x)
  (ormap (λ (f) (f x)) (list answer? var? app? rec? if/? prim-app? mon?)))

;; contract/? : Any -> Boolean
(define (contract/? x)
  (or (flat/c? x) (func/c? x)))
(struct flat/c (exp))
(struct func/c (dom var type rng))

;; type? : Any -> Boolean
;; Type = BaseType | (func-type Type Type) | (con-type Type)
(define (type? x)
  (or (base-type? x) (func-type? x) (con-type? x)))

(struct func-type (from to))
(struct con-type (of))

;; base-type? : Any -> Boolean
;; BaseType = 'Int | 'Bool | '⊥
(define (base-type? x)
  (member x '(Int Bool ⊥)))

;; TypeResult = Type | TypeError
(define (type-result? x)
  (or (type? x) (equal? x 'TypeError)))

;; exp=? : Exp Exp -> Boolean
(define (exp=? x y)
  (e=? (normalize x) (normalize y)))

;; con=? : Contract Contract -> Boolean
(define (con=? c1 c2)
  (c=? (normalize-con c1) (normalize-con c2)))

;; Exp', Contract' are informally defined as 'normalized' versions of
;; Exp and Contract

;; c=? : Contract' Contract' -> Boolean
(define (c=? c1 c2)
  (equal? (show-con (normalize-con c1)) (show-con (normalize-con c2))))

;; e=? : Exp' Exp' -> Boolean
;; compare normalized expressions
(define (e=? e1 e2)
  (equal? (show-exp (normalize e1)) (show-exp (normalize e2))))

;; normalize : Exp -> Exp'
(define (normalize e)
  (normalize-with empty e))

;; normalize-with : [Listof Var] Exp -> Exp'
(define (normalize-with xs e)
  (match e
    [(value u cs)
     (value (match u
              [(lam x t e) (lam 0 0 (normalize-with (cons x xs) e))]
              [else u])
            (map (curry normalize-con-with xs) cs))]
    [(blame/ l1 l2) (blame/ l1 l2)] ; TODO: can we equate all blame/s?
    [(app e1 e2) (app (normalize-with xs e1) (normalize-with xs e2))]
    [(rec f t e) (rec 0 0 (normalize-with (cons f xs) e))]
    [(if/ e1 e2 e3) (if/ (normalize-with xs e1)
                         (normalize-with xs e2)
                         (normalize-with xs e3))]
    [(prim-app o args) (prim-app o (map (curry normalize-with xs) args))]
    [(mon h f g c e) (mon h f g
                          (normalize-con-with xs c)
                          (normalize-with xs e))]
    [else (maybe-var-distance e xs)]))

;; maybe-var-distance : Var [Listof Var] -> Nat or Var
(define (maybe-var-distance x xs)
  ;; go : Nat [Listof Var] -> Nat or Var
  (define (go k xs)
    (match xs
      [(cons z zs) (if (equal? x z) k (go (+ 1 k) zs))]
      [empty x]))
  (go 0 xs))

;; normalize-con : Contract -> Contract'
(define (normalize-con c)
  (normalize-con-with empty c))

;; normalize-con : [Listof Var] Contract -> Contract'
(define (normalize-con-with xs c)
  (match c
    [(flat/c e) (flat/c (normalize-with xs e))]
    [(func/c c x t d) (func/c (normalize-con-with xs c) 0 0
                              (normalize-con-with (cons x xs) d))]))

;; δ : Op [Listof Value] -> [Listof Answer]
;; applies primitive op
(define (δ o xs)
  (if (andmap concrete? xs)
      (list (value (apply (op-impl o) (map value-pre xs)) '{}))
      (match (op-range o)
        ['Int 
         (match o
           ['sqrt `{,(value (opaque 'Int) `{,(read-con c/non-neg)})}]
           [else `{,(value (opaque 'Int) '{})}])]
        ['Bool `{,(value #t '{}) ,(value #f '{})}])))

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
  
  ;; type-check-with : [Listof (list Var Type)] Exp -> TypeResult
  (define (type-check-with tenv e)
    (match e
      [(value (opaque t) refinements) t]
      [(value (lam var type body) refinements)
       (extend func-type type (type-check-with (cons `(,var ,type) tenv) body))]
      [(blame/ l1 l2) '⊥]
      [(app f x) (extend type-app
                         (type-check-with tenv f)
                         (type-check-with tenv x))]
      [(rec var type body) (type-check-with 
                            (cons `(,var ,type) tenv) body)]
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
      [else 
       (if (var? e)
           (match (assoc e tenv)
             [(list x t) t]
             [else 'TypeError])
           'TypeError)]))
  
  ;; type-check-con-with : [Listof (list Var Type)] Contract -> TypeResult
  (define (type-check-con-with tenv c)
    (match c
      [(flat/c e) (match (type-check-with tenv e)
                    [(func-type t 'Bool) (extend con-type t)]
                    [else 'TypeError])]
      [(func/c dom x t rng)
       (match `(,(type-check-con-with tenv dom)
                ,(type-check-con-with (cons `(,x ,t) tenv) rng))
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
       (and (type=? x1 x2) (type=? y1 y2))]
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

;; subst : Var Exp Exp -> Exp
(define (subst x v e)
  ;; go : Exp -> Exp
  (define go (curry subst x v))
  (match e
    [(value u cs)
     (match u
       [(lam z t b)
        (if (equal? x z) e
            (let ([y (variable-not-in (append (free-vars b) (free-vars v)) z)])
              ;; TODO: exponential risk
              (value (lam y t (go (subst z y b))) '{})))]
       [else e])]
    [(blame/ l1 l2) (blame/ l1 l2)]
    [(app e1 e2) (app (go e1) (go e2))]
    [(rec f t b) (if (equal? f x) e
                     (let ([g (variable-not-in (append (free-vars b)
                                                       (free-vars v)) f)])
                       ;; TODO: exponential risk
                       (rec g t (go (subst f g b)))))]
    [(if/ e1 e2 e3) (if/ (go e1) (go e2) (go e3))]
    [(prim-app o args) (prim-app o (map go args))]
    [(mon h f g c e) (mon h f g (subst-con x v c) (go e))]
    [z (if (equal? z x) v z)]))

;; subst-con : Var Exp Contract -> Contract
(define (subst-con x v c)
  ;; go : Contract -> Contract
  (define go (curry subst-con x v))
  (match c
    [(flat/c e) (flat/c (subst x v e))]
    [(func/c c z t d)
     (if (equal? z x)
         (func/c (go c) z t d)
         (let ([y (variable-not-in (append (free-vars v) (con-free-vars d)) z)])
           (func/c (go c) y t
                   ;; TODO: exponential risk
                   (go (subst-con z y d)))))]))

;; free-vars : Exp -> [Listof Var]
(define (free-vars e)
  (match e
    [(value (lam x t b) cs)
     (filter (compose not (curry equal? x))
             (apply append (cons (free-vars b) (map con-free-vars cs))))]
    [(app e1 e2) (append (free-vars e1) (free-vars e2))]
    [(rec x t b) (filter (compose not (curry equal? x)) (free-vars b))]
    [(if/ e1 e2 e3) (append (free-vars e1) (free-vars e2) (free-vars e3))]
    [(prim-app o args) (apply append (map free-vars args))]
    [(mon h f g c e) (append (con-free-vars c) (free-vars e))]
    [x (if (var? x) (list x) empty)]))

;; con-free-vars : Contract -> [Listof Var]
(define (con-free-vars c)
  (match c
    [(flat/c e) (free-vars e)]
    [(func/c c x t d)
     (append (con-free-vars c)
             (filter (compose not (curry equal? x)) (con-free-vars d)))]))

;; read-exp : S-exp -> Exp
(define (read-exp s)
  
  (match s
    [`(• ,t) (value (opaque (read-type t)) empty)]
    [`(λ (,x ,t) ,e) (if (symbol? x)
                         (value (lam x (read-type t) (read-exp e)) empty)
                         (error "λ: expect symbol, given: " x))]
    [`(blame/ ,f ,g) (if (and (symbol? f) (symbol? g))
                         (blame/ f g)
                         (error "blame/: expect symbols, given: " f g))]
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
     (let ([x (variable-not-in d 'z)])
       (func/c (read-con c) x 'Int (read-con d)))]
    [else (error "invalid contract form: " s)]))

;; show-exp : Exp -> S-exp
(define (show-exp e)
  (match e
    [(value (opaque t) _) `(• ,(show-type t))]
    [(value (lam var type body) _)
     `(λ (,var ,(show-type type)) ,(show-exp body))]
    [(blame/ l1 l2) `(blame/ ,l1 ,l2)]
    [(app f x) (map show-exp `(,f ,x))]
    [(rec var type body) `(μ (,var ,(show-type type)) ,(show-exp body))]
    [(if/ e1 e2 e3) `(if ,@(map show-exp `(,e1 ,e2 ,e3)))]
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
(check-equal? (tc keygen) '(Int → Int))
(check-equal? (tc rsa) '(Int → (Int → Int)))
(check-equal? (tc rsa-ap) 'Int)
(check-equal? (tc sqroot) '(Int → Int))
(check-equal? (tc sqrt-user) '((Int → Int) → Int))
(check-equal? (tc sqrt-ap) 'Int)