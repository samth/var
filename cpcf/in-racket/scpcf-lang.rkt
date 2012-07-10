#lang racket
(require redex) ; variable-not-in
(require rackunit)
(require racket/contract)

(require "env.rkt")

(provide
 
 (contract-out
  [struct ref ([distance natural?])]
  [struct val ([pre pre-val?] [refinements (set/c contract-clo?)])]
  
  [struct lam ([body exp?])]
  [struct app ([func exp?] [args (listof exp?)])]
  [struct rec ([body exp?])]
  [struct if/ ([test exp?] [then exp?] [else exp?])]
  [struct mon ([orig label?] [pos label?] [neg label?]
                             [con contract/?] [exp exp?])]
  [struct prim ([name label?])]
  [struct blame/ ([violator label?] [violatee label?])]
  
  [struct flat/c ([exp exp?])]
  [struct func/c ([dom contract/?] [rng contract/?])]
  [struct consc ([car contract/?] [cdr contract/?])]
  [struct orc ([left contract/?] [right contract/?])]
  [struct andc ([left contract/?] [right contract/?])]
  [struct rec/c ([body contract/?])]
  [struct con-ref ([distance natural?])]
  
  ;; hiding closure constructors would make it tedious due to lack of
  ;; pattern matching. But client is expected to use 'close' instead of
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
  
  [shift (natural? exp? . -> . exp?)]
  
  ;[δ (label? op? (listof clo?) . -> . (set/c clo?))]
  
  [read-exp (s-exp? . -> . exp?)]
  [show-exp (exp? . -> . s-exp?)]
  
  [exp? (any/c . -> . boolean?)]
  [answer? (any/c . -> . boolean?)]
  [pre-val? (any/c . -> . boolean?)]
  [label? (any/c . -> . boolean?)]
  [op? (any/c . -> . boolean?)]
  [s-exp? (any/c . -> . boolean?)])
 
 ;; s-map : [x -> y] [Setof x] -> [Setof y]
 s-map
 
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
;; App := (app Exp [Listof Exp])
(struct app exp (func args) #:transparent)
;; Rec := (rec Exp)
(struct rec exp (body) #:transparent)
;; If := (if/ Exp Exp Exp)
(struct if/ exp (test then else) #:transparent)
;; Prim := (prim Label)
(struct prim exp (name) #:transparent)
;; Mon := (mon Label Label label Contract Exp)
(struct mon exp (orig pos neg con exp) #:transparent)

;; Blame := (blame/ Label Label)
(struct blame/ answer (violator violatee) #:transparent)

;; PreVal := • | Number | Boolean | String | Lambda | Nil
(define (pre-val? x)
  (or (eq? x '•) (number? x) (boolean? x) (string? x) (lam? x) (eq? 'nil x)))
;; Lambda := (lambda Exp)
(struct lam (body) #:transparent)

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
(struct func/c contract/ (dom rng) #:transparent)
(struct consc contract/ (car cdr) #:transparent)
(struct orc contract/ (left right) #:transparent)
(struct andc contract/ (left right) #:transparent)
(struct rec/c contract/ (body) #:transparent)
(struct con-ref contract/ (distance) #:transparent)

;; ContractClosure = (contract-clo Contract [Env Val])
(struct contract-clo (con env) #:transparent)

;; close-contract : Contract Env -> ContractClosure
(define (close-contract con en)
  (contract-clo con (env-restrict (con-free-vars con) en)))

;; OpImpl = Label [Listof ValClosure] -> [Setof ANswer]
;; ops : Symbol ↦ (Label [Listof Closure] -> [Setof Answer])
;; primitive ops' types and implementations
(define ops
  (local
    (;; closures for commonly used values
     [define T {set (exp-clo (val #t ∅) ρ0)}]
     [define F {set (exp-clo (val #f ∅) ρ0)}]
     [define TF (set-union T F)]
     
     ;; type-pred : Label Exp (Any -> Boolean) -> OpImpl
     [define (type-pred op-name contract prim-test?)
       (λ (l xs)
         (match xs
           [`(,(exp-clo (val u cs) ρ))
            (match u
              ['• (if (set-member? cs contract) T TF)]
              [c (if (prim-test? u) T F)])]
           [`(,clo) F]
           [_ (set (blame/ l op-name))]))] ; arity mismatch
     
     ;; type predicates defined separately for use in several places
     [define t-any? (λ (l xs) T)]
     [define t-num? (type-pred 'num? (prim 'num?) number?)]
     [define t-real? (type-pred 'real? (prim 'real?) real?)]
     [define t-int? (type-pred 'int? (prim 'int?) integer?)]
     [define t-bool? (type-pred 'bool? (prim 'bool?) boolean?)]
     [define t-string? (type-pred 'string? (prim 'string?) string?)]
     
     ;; contract sets defined separately for use in several places
     [define t-num/c {set (contract-clo (flat/c (prim 'num?)) ρ0)}]
     [define t-real/c (set-add t-num/c
                               (contract-clo (flat/c (prim 'real?)) ρ0))]
     [define t-int/c (set-add t-real/c
                              (contract-clo (flat/c (prim 'int?)) ρ0))]
     [define t-bool/c {set (contract-clo (flat/c (prim 'bool?)) ρ0)}]
     [define t-string/c {set (contract-clo (flat/c (prim 'string?)) ρ0)}]
     
     ;; concrete? : ValClosure -> Bool
     ;; checks whether a closure represents a concrete value
     (define (concrete? cl)
       (match cl
         [(exp-clo (val u cs) ρ) (not (equal? u '•))]
         [_ #f]))
     
     ;; mk-op : Label [Listof TypePred] [PreVal -> PreVal] [Setof ContractClosure]
     ;;      -> OpImpl
     ;; makes fix-arity operator on non-pair values
     [define (mk-op name dom-tests prim-op refinements)
       (λ (l xs)
         (let ([dom-oks (map (λ (test x) (test l (list x))) dom-tests xs)])
           (set-union
            (if (ormap (curry subset? F) dom-oks)
                {set (exp-clo (blame/ l name) ρ0)}
                ∅)
            (if (andmap (curry subset? T) dom-oks)
                (if (andmap concrete? xs)
                    (exp-clo
                     (val
                      (apply prim-op l (map (compose val-pre exp-clo-exp) xs))
                      ∅)
                     ρ0)
                    (exp-clo (val '• refinements) ρ0))
                ∅))))]
     )
    
    (hash
     ;; type predicates
     'num? t-num?
     'real? t-real?
     'int? t-int?
     'bool? t-bool?
     'string? t-string?
     'true? (type-pred 'true? (prim 'true?) (compose not false?))
     'false? (type-pred 'false? (prim 'false?) false?)
     'nil? (λ (l xs)
             (match xs
               [`(,(exp-clo (val u cs) ρ))
                (match u
                  ['nil T]
                  ['• (if (set-member? cs (prim 'nil?)) T TF)]
                  [_ F])]
               [`(,clo) F]
               [_ (set (blame/ l 'nil?))])) ; arity mismatch
     'cons? (λ (l xs)
              (match xs
                [`(,(exp-clo (val '• cs) ρ))
                 (if (set-member? cs (prim 'cons?)) T TF)]
                [`(,(cons-clo c1 c2)) T]
                [`(,clo) F]
                [_ (set (blame/ l 'cons?))])) ; arity mismatch
     
     'zero? (mk-op 'zero? `(,t-num?) zero? t-num/c)
     'non-neg? (mk-op 'non-neg? `(,t-real?) (curry <= 0) t-bool/c)
     'even? (mk-op 'even? `(,t-int?) even? t-bool/c)
     'odd? (mk-op 'odd? `(,t-int?) odd? t-bool/c)
     'prime? (mk-op 'prime? `(,t-int?)
                    (λ (n) (if (member n '(2 3 5 7 11 13)) #t #f))
                    t-bool/c)
     'not (mk-op 'not `(,t-any?) (λ (v) (if (false? v) #t #f)) t-bool/c)
     'sqrt (mk-op 'sqrt `(,t-num?) sqrt t-num/c)
     
     ;; TODO: extend ops to var-arg, maybe with fold on bin-ops? potentially slow...
     '+ (mk-op '+ `(,t-num? ,t-num?) + t-num/c)
     '- (mk-op '- `(,t-num? ,t-num?) - t-num/c)
     '* (mk-op '* `(,t-num? ,t-num?) * t-num/c)
     '= (mk-op '= `(,t-num? ,t-num?) = t-bool/c)
     '≠ (mk-op '≠ `(,t-num? ,t-num?) (compose not =) t-bool/c)
     '< (mk-op '< `(,t-real? ,t-real?) < t-bool/c)
     '≤ (mk-op '≤ `(,t-real? ,t-real?) <= t-bool/c)
     '> (mk-op '> `(,t-real? ,t-real?) > t-bool/c)
     '≥ (mk-op '≥ `(,t-real? ,t-real?) >= t-bool/c)
     '++ (mk-op '++ `(,t-string? ,t-string?) string-append t-string/c)
     'str=? (mk-op 'str=? `(,t-string? ,t-string?) string=? t-bool/c)
     'str≠? (mk-op 'str≠? `(,t-string? ,t-string?) (compose not string=?) t-bool/c)
     'str<? (mk-op 'str<? `(,t-string? ,t-string?) string<? t-bool/c)
     'str≤? (mk-op 'str≤? `(,t-string? ,t-string?) string<=? t-bool/c)
     'str>? (mk-op 'str>? `(,t-string? ,t-string?) string>? t-bool/c)
     'str≥? (mk-op 'str≥? `(,t-string? ,t-string?) string>=? t-bool/c)
     'str-len (mk-op 'str-len `(,t-string?) string-length t-int/c)
     'substring (mk-op 'substring `(,t-string? ,t-int? ,t-int?)
                       (match-lambda
                         [`(,s ,i_0 ,i_n) ; TODO: restructure mk-op, maybe
                          (if (<= i_0 i_n)
                              (substring s
                                         (max 0 i_0)
                                         (min (string-length s) i_n))
                              "")])
                       t-string/c)
     'cons (λ (l xs)
             {set (match xs
                    [`(,c1 ,c2) (cons-clo c1 c2)]
                    [_ (blame/ l 'cons)])}) ; arity mismatch
     'car (λ (l xs)
            (match xs
              [`(,(cons-clo c1 c2)) {set c1}]
              [`(,(exp-clo (val u cs) ρ))
               (let ([c-list (set->list cs)])
                 ;; TODO: also consider case with weaker contract 'cons?'
                 (match (memf consc? c-list)
                   [`(,(consc c1 c2) ,_...) {set (exp-clo (val '• {set c1}) ρ0)}]
                   [_ {set (exp-clo (val '• ∅) ρ0)
                           (exp-clo (blame/ l 'car) ρ0)}]))]
              [_ {set (exp-clo (blame/ 'l 'car) ρ0)}]))
     'cdr (λ (l xs)
            (match xs
              [`(,(cons-clo c1 c2)) {set c2}]
              [`(,(exp-clo (val u cs) ρ))
               (let ([c-list (set->list cs)])
                 ;; TODO: also consider case with weaker contract 'cons?'
                 (match (memf consc? c-list)
                   [`(,(consc c1 c2) ,_...) {set (exp-clo (val '• {set c2}) ρ0)}]
                   [_ {set (exp-clo (val '• ∅) ρ0)
                           (exp-clo (blame/ l 'cdr) ρ0)}]))]
              [_ {set (exp-clo (blame/ 'l 'cdr) ρ0)}])))))

;; free-vars : Exp -> [Setof Natural]
(define (free-vars e)
  (vars≥ 0 e))
;; vars≥ : Exp -> [Setof Natural]
(define (vars≥ d e)
  (match e
    [(ref k) (if (>= k d) {set (- k d)} ∅)]
    [(val u cs) (match u
                  [(lam b) (vars≥ (+ 1 d) b)]
                  [else ∅])]
    [(blame/ l1 l2) ∅]
    [(app f xs) (set-union (vars≥ d f)
                           (apply set-union (map (curry vars≥ d) xs)))]
    [(rec b) (vars≥ (+ 1 d) b)]
    [(if/ e1 e2 e3) (set-union (vars≥ d e1) (vars≥ d e2) (vars≥ d e3))]
    [(prim _) ∅]
    [(mon h f g c e) (set-union (con-vars≥ d c) (vars≥ d e))]))
;; con-free-vars : Contract -> [Setof Natural]
(define (con-free-vars c)
  (con-vars≥ 0 c))
;; con-vars≥ : Natural Contract -> [Setof Natural]
(define (con-vars≥ d c)
  (match c
    [(flat/c e) (vars≥ d e)]
    [(func/c c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ (+ 1 d) c2))]
    [(consc c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(orc c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(andc c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(rec/c c) (con-vars≥ (+ 1 d) c)]
    [(con-ref x) (if (>= x d) {set (- x d)} ∅)]))

;; read-exp : S-exp -> Exp
(define (read-exp s)
  (read-exp-with empty s))

;; read-con : S-exp -> Contract
(define (read-con s)
  (read-con-with empty s))

;; read-con-with : [Listof Symbol] S-exp -> Contract
(define (read-con-with names s)
  (match s
    [`(flat ,e) (flat/c (read-exp-with names e))]
    [`(,c ↦ (λ (,x ,t) ,d))
     (if (symbol? x)
         (func/c (read-con-with names c)
                 (read-con-with (cons x names) d))
         (error "function contract: expect symbol, given: " x))]
    [`(,c ↦ ,d)
     (let ([x (variable-not-in d 'z)]) ; desugar independent contract
       (read-con-with names `(,c ↦ (λ (,x Num) ,d))))]
    [`(cons/c ,c ,d) (consc (read-con-with names c) (read-con-with names d))]
    [`(,c ∨ ,d) (orc (read-con-with names c) (read-con-with names d))]
    [`(,c ∧ ,d) (andc (read-con-with names c) (read-con-with names d))]
    [`(μ (,x ,t) ,c) (rec/c (read-con-with (cons x names) c))]
    [x (if (symbol? x)
           (let ([d (name-distance x names)])
             (if (<= 0 d) 
                 (con-ref d)
                 (error "unbound: " x)))
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
    [`• (val '• ∅)]
    [`(λ (,x) ,s) (if (symbol? x)
                      (val (lam (read-exp-with (cons x names) s)) ∅)
                      (error "λ: expect symbol, given: " x))]
    [`(blame ,f ,g) (if (and (symbol? f) (symbol? g))
                        (blame/ f g)
                        (error "blame: expect symbols, given: " f g))]
    [`(μ (,f) ,s) (if (symbol? f)
                      (rec (read-exp-with (cons f names) s))
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
    [`(,sf ,sxs ...) (app (read-exp-with names sf)
                          (map (curry read-exp-with names) sxs))]
    [x (cond
         [(pre-val? x) (val x ∅)]
         [(symbol? x)
          (let ([d (name-distance x names)])
            (if (<= 0 d)
                (ref d)
                (if (op? x)
                    (prim x)
                    (error "unbound: " x))))]
         [else (error "invalid expression form: " x)])]))

;; show-exp : Exp -> S-exp
(define (show-exp e)
  
  ;; new-var-name : [Listof Symbol] -> Symbol
  (define (new-var-name used-names)
    (let ([pool '(x y z a b c w u v m n)])
      (match (filter (λ (n) (not (member n used-names))) pool)
        [(cons name names) name]
        [empty (variable-not-in used-names (first pool))])))
  
  ;; show-exp-with : [Listof Symbol] -> S-exp
  (define (show-exp-with names e)
    (match e
      [(ref d) (list-ref names d)] ;; closed expressions can't cause error
      [(val u _)
       (match u
         [(lam b) 
          (let ([x (new-var-name names)])
            `(λ (,x) ,(show-exp-with (cons x names) b)))]
         [c c])]
      [(blame/ l1 l2) `(blame l1 l2)]
      [(app func args) (cons (show-exp-with names func)
                             (map (curry show-exp-with names) args))]
      [(rec b)
       (let ([f (new-var-name names)])
         `(μ (,f) ,(show-exp-with (cons f names) b)))]
      [(if/ e1 e2 e3) `(if ,@(map (curry show-exp-with names) `(,e1 ,e2 ,e3)))]
      [(prim name) name]
      [(mon h f g c e) `(mon ,h ,f ,g
                             ,(show-con-with names c)
                             ,(show-exp-with names e))]))
  
  ;; show-con-with : [Listof Symbol] Contract -> S-exp
  (define (show-con-with names c)
    (match c
      [(flat/c e) `(flat ,(show-exp-with names e))]
      [(func/c c d)
       `(,(show-con-with names c)
         ↦
         ,(let ([x (new-var-name names)])
            `(λ (,x) ,(show-con-with (cons x names) d))))]
      [(consc c d) `(consc ,(show-con-with names c) ,(show-con-with names d))]
      [(orc c d) `(,(show-con-with names c) ∨ ,(show-con-with names d))]
      [(andc c d) `(,(show-con-with names c) ∧ ,(show-con-with names d))]
      [(rec/c c) (let ([x (new-var-name names)])
                   `(μ (,x) ,(show-con-with (cons x names) c)))]
      [(con-ref d) (list-ref names d)]))
  
  (show-exp-with empty e))

;; name-distance : Symbol [Listof Symbol] -> Natural or -1 if name not bound
(define (name-distance x xs)
  ;; go : Natural [Listof Symbol] -> Natural
  (define (go pos xs)
    (match xs
      [(cons z zs) (if (equal? z x) pos (go (+ 1 pos) zs))]
      [empty -1]))
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
         [(lam b) (val (lam (shift-at (+ 1 depth) b)) cs)]
         [_ e])]
      [(blame/ l1 l2) e]
      [(app func exps) (app (shift-at depth func)
                            (map (curry shift-at depth) exps))]
      [(rec b) (rec (shift-at (+ 1 depth) b))]
      [(if/ e1 e2 e3)
       (if/ (shift-at depth e1) (shift-at depth e2) (shift-at depth e3))]
      [(prim name) (prim name)]
      [(mon h f g c e) (mon h f g (shift-con-at depth c) (shift-at depth e))]))
  
  ;; shift-con-at : Natural Contract -> Contract
  (define (shift-con-at depth c)
    (match c
      [(flat/c e) (flat/c (shift-at depth e))]
      [(func/c c1 c2)
       (func/c (shift-con-at depth c1) (shift-con-at (+ 1 depth) c2))]
      [(consc c1 c2) (consc (shift-con-at depth c1) (shift-con-at depth c2))]
      [(orc c1 c2) (orc (shift-con-at depth c1) (shift-con-at depth c2))]
      [(andc c1 c2) (andc (shift-con-at depth c1) (shift-con-at depth c2))]
      [(rec/c c1) (rec/c (shift-con-at (+ 1 depth) c1))]
      [(con-ref x) (if (>= x depth) (con-ref (+ x d)) c)]))
  
  (shift-at 0 e))

;;;; set helper functions

;; s-map : [x -> y] [Setof x] -> [Setof y]
(define (s-map f xs)
  #;(for/set ([x xs]) (f x))
  ; TODO: is this how I use in-set?
  (for/fold ([ys ∅]) ([x (in-set xs)]) (set-add ys (f x))))