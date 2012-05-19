#lang racket

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
;; O1 = zero? | non-neg? | even? | odd? | prime? | true? | false? | sqrt
;; O2 = + | -

(struct mon (origin pos neg con exp))
;; Mon = (mon Label Label Label Contract Exp)

;; Label = Symbol
(define label? symbol?)

(struct blame (violator violatee))
;; Blame = (blame Label Label)

;; Contract = (flat/c Exp) | (func/c Var Type Exp)
(struct flat/c (exp))
(struct func/c (x body))

;; Type = BaseType | (func-type Type Type) | (con-type Type)
(struct func-type (from to))
(struct con-type (of))
;; BaseType = 'Int | 'Bool | '⊥

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

;; i have a procedure with 11 parameters. I probably missed some...
;; how would experienced programmers deal with this?
;; foldE : #:on-opauqe (Type -> a)
;;         #:on-int (Integer -> a)
;;         #:on-bool (Boolean -> a)
;;         #:on-λ (Var Type a -> a)
;;         #:on-blame  (Label Label -> a)
;;         #:on-var (Var -> a)
;;         #:on-app (a a -> a)
;;         #:on-μ (Var Type a -> a)
;;         #:on-if (a a a -> a)
;;         #:on-prim (o (Listof a) -> a)
;;         #:on-mon (Label Label Label Contract a -> a)
;;         Exp -> a
(define (foldE #:on-opaque on-opaque
               #:on-int on-int
               #:on-bool on-bool
               #:on-λ on-λ
               #:on-blame on-blame
               #:on-var on-var
               #:on-app on-app
               #:on-μ on-μ
               #:on-if on-if
               #:on-prim on-prim
               #:on-mon on-mon
               e)
  (define go (curry foldE #:on-opaque on-opaque
                    #:on-int on-int
                    #:on-bool on-bool
                    #:on-λ on-λ
                    #:on-blame on-blame
                    #:on-var on-var
                    #:on-app on-app
                    #:on-μ on-μ
                    #:on-if on-if
                    #:on-prim on-prim
                    #:on-mon on-mon))
  (match e
    [(opaque t) (on-opaque t)]
    [(lam var type body) (on-λ var type (go body))]
    [(blame l1 l2) (on-blame l1 l2)]
    [(app f x) (on-app (go f) (go x))]
    [(rec var type body) (on-μ var type (go body))]
    [(if/ e1 e2 e3) (on-if (go e1) (go e2) (go e3))]
    [(prim-app o args) (on-prim o (map go args))]
    [(mon h f g con e) (on-mon h f g con (go e))]
    [else (cond
            [(integer? e) (on-int e)]
            [(boolean? e) (on-bool e)]
            [(var? e) (on-var e)])]))