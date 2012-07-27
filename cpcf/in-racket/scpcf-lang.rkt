#lang racket
(require redex) ; variable-not-in
(require rackunit)
(require racket/contract)

(require "env.rkt")

(provide
 
 (contract-out
  [struct prog ([modules (listof modl?)] [main exp?])]
  [struct modl ([f label?] [c contract/?] [v exp?])]
  
  [struct ref ([distance natural?])]
  [struct val ([pre pre-val?] [refinements (set/c contract-cl?)])]
  
  [struct lam ([arity natural?] [body exp?])]
  [struct app ([func exp?] [args (listof exp?)] [lab label?])]
  [struct rec ([body exp?])]
  [struct if/ ([test exp?] [then exp?] [else exp?])]
  [struct mon ([orig label?] [pos label?] [neg label?]
                             [con contract/?] [exp exp?])]
  [struct blame/ ([violator label?] [violatee label?])]
  [struct mod-ref ([f label?] [l label?])]
  
  [struct flat-c ([exp exp?])]
  [struct func-c ([dom (listof contract/?)] [rng contract/?])]
  [struct cons-c ([car contract/?] [cdr contract/?])]
  [struct or-c ([left contract/?] [right contract/?])]
  [struct and-c ([left contract/?] [right contract/?])]
  [struct rec-c ([body contract/?])]
  [struct ref-c ([distance natural?])]
  
  ;; hiding closure constructors would make it tedious due to lack of
  ;; pattern matching. But client is expected to use 'close' instead of
  ;; 'exp-cl', and 'close-contract' instead of 'contract-cl'
  [struct exp-cl ([exp exp?] [env env?])]
  [struct mon-fn-cl ([orig label?] [pos label?] [neg label?]
                                   [con (struct/c contract-cl func-c? env?)]
                                   [exp clo?])]
  [struct cons-cl ([car clo?] [cdr clo?])]
  [struct contract-cl ([con contract/?] [env env?])]
  [clo? (any/c . -> . boolean?)]
  [close (exp? env? . -> . clo?)]
  [close-contract (contract/? env? . -> . contract-cl?)]
  [val-cl? (any/c . -> . boolean?)]
  
  [shift (natural? exp? . -> . exp?)]
  
  [δ (op? (listof clo?) label? . -> . (set/c clo?))]
  [split-cons (val-cl? . -> . (set/c (or/c empty? (list/c val-cl? val-cl?))))]
  
  [read-prog (s-exp? . -> . prog?)]
  [show-prog (prog? . -> . s-exp?)]
  [read-exp (s-exp? . -> . exp?)]
  [show-exp (exp? . -> . s-exp?)]
  
  [mod-by-name (label? [listof modl?] . -> . modl?)]
  
  [proc-with-arity? (val-cl? natural? . -> . (set/c boolean?))]
  
  [exp? (any/c . -> . boolean?)]
  [answer? (any/c . -> . boolean?)]
  [pre-val? (any/c . -> . boolean?)]
  [label? (any/c . -> . boolean?)]
  [op? (any/c . -> . boolean?)]
  [s-exp? (any/c . -> . boolean?)])
 
 c/any c/bool c/list c/num-list c/even-list c/bool-list
 
 ;; s-map : [x -> y] [Setof x] -> [Setof y]
 s-map
 
 ;; non-det : (x -> [Setof y]) [Setof x] -> [Setof y]
 non-det
 ∅)

;; ∅ : Setof x
;; (eq? (set) (set)) = #f, and we have a lot of empty sets around,
;; so I guess this might be useful. It looks nicer anyway.
(define ∅ (set))

;; s-exp? : Any -> Boolean
(define s-exp? any/c) ; TODO

;; Prog := (prog [Listof Module] Exp)
(struct prog (modules main) #:transparent)
;; Module := (modl Label Contract Value)
(struct modl (f c v) #:transparent)

(struct exp () #:transparent)
(struct answer exp () #:transparent)
;; Val := (val Preval [Listof ContractClosure])
(struct val answer (pre refinements) #:transparent)
;; Ref := (ref Natural)
(struct ref exp (distance) #:transparent)
;; App := (app Exp [Listof Exp] Label)
(struct app exp (func args lab) #:transparent)
;; Rec := (rec Exp)
(struct rec exp (body) #:transparent)
;; If := (if/ Exp Exp Exp)
(struct if/ exp (test then else) #:transparent)
;; Mon := (mon Label Label label Contract Exp)
(struct mon exp (orig pos neg con exp) #:transparent)
;; ModRef := (mod-ref Label Label)
(struct mod-ref exp (f l) #:transparent) ; reference to f from l

;; Blame := (blame/ Label Label)
(struct blame/ answer (violator violatee) #:transparent)

;; PreVal := • | Number | Boolean | String | Lambda | Nil
(define (pre-val? x)
  (or (eq? x '•) (number? x) (boolean? x) (string? x) (lam? x) (eq? 'nil x) (op? x)))
;; Lambda := (lambda Natural Exp)
(struct lam (arity body) #:transparent)

;; Closure := ExpClosure | MonFnClosure | ConsClosure
(struct clo () #:transparent)
;; ExpClosure := (exp-cl Exp Env)
(struct exp-cl clo (exp env) #:transparent)
;; MonFnClosure := (mon-fn-cl Label Label Label ContractClosure Closure)
(struct mon-fn-cl clo (orig pos neg con exp) #:transparent)
;; ConsClosure := (cons-cl Closure Closure)
(struct cons-cl clo (car cdr) #:transparent)

;; close : Exp Env -> Closure
;; closes expression with given environment, dropping all unused closures
(define (close exp en)
  (exp-cl exp (env-restrict (free-vars exp) en)))

;; val-cl? : Closure -> Boolean
;; checks whether closure represents a value
(define (val-cl? clo)
  (or (and (exp-cl? clo) (val? (exp-cl-exp clo)))
      (mon-fn-cl? clo)
      (cons-cl? clo)))

;; checks whether symbol names a primitive op
(define (op? o)
  (hash-has-key? ops o))

;; label? : Any -> Boolean
(define label? symbol?)

;; Contract := FlatContract | FuncContract | ConsContract
;;           | OrContract | AndContract | RecContract
(struct contract/ () #:transparent)
(struct flat-c contract/ (exp) #:transparent)
(struct func-c contract/ (dom rng) #:transparent)
(struct cons-c contract/ (car cdr) #:transparent)
(struct or-c contract/ (left right) #:transparent)
(struct and-c contract/ (left right) #:transparent)
(struct rec-c contract/ (body) #:transparent)
(struct ref-c contract/ (distance) #:transparent)

;; ContractClosure = (contract-cl Contract [Env Val])
(struct contract-cl (con env) #:transparent)

;; close-contract : Contract Env -> ContractClosure
(define (close-contract con en)
  (contract-cl con (env-restrict (con-free-vars con) en)))

;; commonly re-used values
(define TRUE (val #t ∅))
(define CL-TRUE (exp-cl TRUE ρ0))
(define FALSE (val #f ∅))
(define CL-FALSE (exp-cl FALSE ρ0))
(define BULLET (val '• ∅))
(define CL-BULLET (exp-cl BULLET ρ0))

;; contracts
(define c/any `(flat (λ (x) #t)))
(define c/bool `(flat bool?))
(define c/list `(μ (list?) (or/c (flat nil?) (cons/c ,c/any list?))))
(define c/num-list `(μ (num-list?) (or/c (flat nil?) (cons/c (flat num?) num-list?))))
(define c/even-list `(μ (evens?) (or/c (flat nil?) (cons/c (flat even?) evens?))))
(define c/bool-list `(μ (bools?) (or/c (flat nil?) (cons/c (flat bool?) bools?))))

;; mk-contract-cl : Pred -> ContractClosure
;; makes contract out of primitive predicate
(define (mk-contract-cl name)
  (contract-cl (flat-c (val name ∅)) ρ0))

;; OpImpl := (op-impl (Nat -> Bool) (Lab [Listof ValClosure] -> [Setof ValClosure])
(struct op-impl (arity-check proc))

;; contracts-imply? : [Setof Contract] Pred -> [Setof (Refuted|Proved)]
;; checks whether set of refinements is enough to prove or refute given
;; primitive predicate
(define (contracts-imply? cs p)
  (let ([excludes (exclude p)]
        [proves (what-imply p)])
    (for/set ([c cs])
             (match c
               [(contract-cl (flat-c (val p cs1)) ρc)
                (cond
                  [(set-member? excludes p) 'Refuted]
                  [(set-member? proves p) 'Proved]
                  [else 'Neither])]
               [_ 'Neither]))))




;; free-vars : Exp -> [Setof Natural]
(define (free-vars e)
  (vars≥ 0 e))
;; vars≥ : Exp -> [Setof Natural]
(define (vars≥ d e)
  (match e
    [(ref k) (if (>= k d) {set (- k d)} ∅)]
    [(val u cs) (match u
                  [(lam n b) (vars≥ (+ n d) b)]
                  [else ∅])]
    [(blame/ l1 l2) ∅]
    [(app f xs l) (set-union (vars≥ d f)
                             (if (empty? xs) ∅
                                 ; why doesn't set-union handle 0 arg?
                                 (apply set-union (map (curry vars≥ d) xs))))]
    [(rec b) (vars≥ (+ 1 d) b)]
    [(if/ e1 e2 e3) (set-union (vars≥ d e1) (vars≥ d e2) (vars≥ d e3))]
    [(mon h f g c e) (set-union (con-vars≥ d c) (vars≥ d e))]
    [(mod-ref f l) ∅]))
;; con-free-vars : Contract -> [Setof Natural]
(define (con-free-vars c)
  (con-vars≥ 0 c))
;; con-vars≥ : Natural Contract -> [Setof Natural]
(define (con-vars≥ d c)
  (match c
    [(flat-c e) (vars≥ d e)]
    [(func-c cs1 c2) (set-union (apply set-union (map (curry con-vars≥ d) cs1))
                                (con-vars≥ (+ (length cs1) d) c2))]
    [(cons-c c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(or-c c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(and-c c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(rec-c c) (con-vars≥ (+ 1 d) c)]
    [(ref-c x) (if (>= x d) {set (- x d)} ∅)]))

;; read-prog : S-exp -> Prog
(define read-prog
  (match-lambda
    [`(,m ... ,e) (prog (map read-modl m) (read-exp e))]
    [x (error "invalid program form: " x)]))

;; read-modl : S-exp -> Module
(define read-modl
  (match-lambda
    [`(module ,f ,c ,v) (modl f (read-con-with '() f c) (read-exp-with '() f v))]
    [x (error "invlaid module form: " x)]))

;; read-exp : S-exp -> Exp
(define (read-exp s)
  (read-exp-with '() '† s))

;; read-con : S-exp -> Contract
(define (read-con s)
  (read-con-with '() '† s))

;; read-con-with : [Listof Symbol] Label S-exp -> Contract
(define (read-con-with names mod s)
  (match s
    [`(flat ,e) (flat-c (read-exp-with names mod e))]
    [`(,cs ... ↦ (λ (,xs ...) ,d))
     (if ((listof symbol?) xs)
         (func-c (map (curry read-con-with names mod) cs)
                 (read-con-with (extend-names xs names) mod d))
         (error "function contract: expect symbols, given: " xs))]
    [`(,cs ... ↦ ,d)
     (let ([xs (variables-not-in d (map (const 'z) cs))]) ; desugar independent contract
       (read-con-with names mod (append cs `(↦ (λ ,xs ,d)))))]
    [`(cons/c ,c ,d)
     (cons-c (read-con-with names mod c) (read-con-with names mod d))]
    [`(or/c ,c ,d) (or-c (read-con-with names mod c) (read-con-with names mod d))]
    [`(and/c ,c ,d) (and-c (read-con-with names mod c) (read-con-with names mod d))]
    [`(μ (,x) ,c) (rec-c (read-con-with (cons x names) mod c))]
    [x (if (symbol? x)
           (let ([d (name-distance x names)])
             (if (<= 0 d)
                 (ref-c d)
                 (error "unbound: " x)))
           (error "invalid contract form: " x))]))

;; read-exp-with : [Listof Symbol] Label S-exp -> Exp
(define (read-exp-with names mod s)
  
  ;; read-and : [Listof S-exp] -> Exp
  (define (read-and terms)
    (match terms
      [`(,t1 ,t2 ,ts ...) (if/ (read-exp-with names mod t1)
                               (read-and (rest terms))
                               FALSE)]
      [`(,t) (read-exp-with names mod t)]
      [`() TRUE]))
  
  ;; read-or : [Listof S-exp] -> Exp
  (define (read-or terms)
    (match terms
      [`(,t1 ,t2 ,ts ...) (if/ (read-exp-with names mod t1)
                               TRUE
                               (read-or (rest terms)))]
      [`(,t) (read-exp-with names mod t)]
      [`() FALSE]))
  
  (match s
    [`• BULLET]
    [`(λ (,xs ...) ,s)
     (if ((listof symbol?) xs)
         (val (lam (length xs) (read-exp-with (extend-names xs names) mod s)) ∅)
         (error "λ: expect symbols, given: " xs))]
    [`(μ (,f) ,s) (if (symbol? f)
                      (rec (read-exp-with (cons f names) mod s))
                      (error "μ: expect symbol, given: " f))]
    [`(if ,s1 ,s2 ,s3) (if/ (read-exp-with names mod s1)
                            (read-exp-with names mod s2)
                            (read-exp-with names mod s3))]
    [`(and ,terms ...) (read-and terms)]
    [`(or ,terms ...) (read-or terms)]
    [`(let ([,x ,e] ...) ,b) (read-exp-with names mod `((λ ,x ,b) ,@e))]
    [`(let* ([,x1 ,e1] ,p ...) ,b)
     (read-exp-with names mod `(let ([,x1 ,e1]) (let* ,p ,b)))]
    [`(let* () ,b) (read-exp-with names mod `(let () ,b))]
    [`(,f ,xs ...) (app (read-exp-with names mod f)
                        (map (curry read-exp-with names mod) xs) mod)]
    [x (cond
         [(boolean? x) (if x TRUE FALSE)]
         [(symbol? x) (let ([d (name-distance x names)])
                        (if (<= 0 d)
                            (ref d)
                            (if (op? x)
                                (val x ∅) ; TODO clean up
                                (if (not (pre-val? x))
                                    (mod-ref x mod)
                                    (val x ∅)))))]
         [(pre-val? x) (val x ∅)]
         [else (error "invalid expression form: " x)])]))

;; extend-names : [Listof Label] [Listof Label] -> [Listof Label]
(define (extend-names new-names old-names)
  (foldl cons old-names new-names))

;; show-prog : Prog -> S-exp
(define show-prog
  (match-lambda
    [(prog modules main) (append (map show-modl modules) (list (show-exp main)))]))

;; show-modl : Module -> S-exp
(define show-modl
  (match-lambda
    [(modl f c v) `(module ,f ,(show-con c) ,(show-exp v))]))

;; show-exp : Exp -> S-exp
(define (show-exp e)
  (show-exp-with '() e))

;; show-con : Contract -> S-exp
(define (show-con c)
  (show-con-with '() c))

;; show-exp-with : [Listof Symbol] -> S-exp
(define (show-exp-with names e)
  (match e
    [(ref d) (list-ref names d)] ;; closed expressions can't cause error
    [(val u _)
     (match u
       [(lam n b) 
        (let ([xs (new-var-names n names)])
          `(λ ,xs ,(show-exp-with (extend-names xs names) b)))]
       [c c])]
    [(blame/ l1 l2) `(blame l1 l2)]
    [(app f xs l) (cons (show-exp-with names f)
                        (map (curry show-exp-with names) xs))]
    [(rec b)
     (let ([f (new-var-name names)])
       `(μ (,f) ,(show-exp-with (cons f names) b)))]
    [(if/ e1 e2 e3) `(if ,@(map (curry show-exp-with names) `(,e1 ,e2 ,e3)))]
    [(mon h f g c e) `(mon ,h ,f ,g
                           ,(show-con-with names c)
                           ,(show-exp-with names e))]
    [(mod-ref f l) f]))

;; show-con-with : [Listof Symbol] Contract -> S-exp
(define (show-con-with names c)
  (match c
    [(flat-c e) `(flat ,(show-exp-with names e))]
    [(func-c cs d)
     (append (map (curry show-con-with names) cs)
             `(↦ ,(let ([xs (new-var-names (length cs) names)])
                    `(λ ,xs ,(show-con-with (extend-names xs names) d)))))]
    [(cons-c c d) `(cons/c ,(show-con-with names c) ,(show-con-with names d))]
    [(or-c c d) `(or/c ,(show-con-with names c) ,(show-con-with names d))]
    [(and-c c d) `(and/c ,(show-con-with names c) ,(show-con-with names d))]
    [(rec-c c) (let ([x (new-var-name names)])
                 `(μ (,x) ,(show-con-with (cons x names) c)))]
    [(ref-c d) (list-ref names d)]))

;; new-var-names : Natural [Listof Symbol] -> Symbol
(define (new-var-names n used-names)
  (if (zero? n) '()
      (let ([x (new-var-name used-names)])
        (cons x (new-var-names (- n 1) (cons x used-names))))))

;; new-var-name : [Listof Symbol] -> Symbol
(define (new-var-name used-names)
  (let ([pool '(x y z a b c w u v m n)])
    (match (filter (λ (n) (not (member n used-names))) pool)
      [(cons name names) name]
      ['() (variable-not-in used-names (first pool))])))

;; name-distance : Symbol [Listof Symbol] -> Natural or -1 if unbound
(define (name-distance x xs)
  ;; go : Natural [Listof Symbol] -> Natural
  (define (go pos xs)
    (match xs
      [(cons z zs) (if (equal? z x) pos (go (+ 1 pos) zs))]
      ['() -1]))
  (go 0 xs))

;; shift : Natural Exp -> Exp
;; shifts free variables in expression by given number
(define (shift ∆ e)
  (shift-at ∆ 0 e))

;; shift-at : Natural Exp -> Exp
(define (shift-at ∆ depth e)
  (match e
    [(ref x) (if (>= x depth) (ref (+ x ∆)) e)]
    [(val u cs)
     (match u
       [(lam n b) (val (lam n (shift-at ∆ (+ n depth) b)) cs)]
       [_ e])]
    [(blame/ l1 l2) e]
    [(app f xs l) (app (shift-at ∆ depth f) (map (curry shift-at depth) xs) l)]
    [(rec b) (rec (shift-at ∆ (+ 1 depth) b))]
    [(if/ e1 e2 e3)
     (if/ (shift-at ∆ depth e1) (shift-at ∆ depth e2) (shift-at ∆ depth e3))]
    [(mon h f g c e) (mon h f g (shift-con-at ∆ depth c) (shift-at ∆ depth e))]
    [(mod-ref f l) e]))

;; shift-con : Natural Contract -> Contract
(define (shift-con ∆ c)
  (shift-con-at ∆ 0 c))

;; shift-con-at : Natural Natural Contract -> Contract
(define (shift-con-at ∆ depth c)
  (match c
    [(flat-c e) (flat-c (shift-at ∆ depth e))]
    [(func-c cs1 c2)
     (func-c (map (curry shift-con-at ∆ depth) cs1)
             (shift-con-at ∆ (+ (length cs1) depth) c2))]
    [(cons-c c1 c2) (cons-c (shift-con-at ∆ depth c1) (shift-con-at ∆ depth c2))]
    [(or-c c1 c2) (or-c (shift-con-at ∆ depth c1) (shift-con-at ∆ depth c2))]
    [(and-c c1 c2) (and-c (shift-con-at ∆ depth c1) (shift-con-at ∆ depth c2))]
    [(rec-c c1) (rec-c (shift-con-at ∆ (+ 1 depth) c1))]
    [(ref-c x) (if (>= x depth) (ref-c (+ x ∆)) c)]))

;; mod-by-name : Label [Listof Module] -> Module
(define (mod-by-name l ms)
  (match ms
    [(cons m ms1) (if (equal? (modl-f m) l) m
                      (mod-by-name l ms1))]
    [_ (error "unbound module name: " l)]))

;; proc-with-arity? : ValClosure Natural -> [Setof Boolean]
;; checks whether closure represents a procedure compatible with given number of args
(define (proc-with-arity? cl n)
  (match cl
    [(exp-cl (val u cs) ρ)
     (match u
       [(lam m e) {set (= m n)}]
       ['• (set-subtract {set #t #f}
                         (for/set ([c cs] #:when (func-c? (contract-cl-con c)))
                                  (match-let ([(contract-cl (func-c cs1 c2) _) c])
                                    (not (= n (length cs1))))))]
       [_ {set (if (op? u)
                   ((op-impl-arity-check (hash-ref ops u)) n)
                   #f)}])]
    [(mon-fn-cl h f g (contract-cl (func-c cs1 c2) ρc) cl1)
     {set (= n (length cs1))}]
    [_ {set #f}]))



;; mechanism for proving primitive predicates

(define rules
  ;; (...p?... ⇒ ...q?...) means ((or ... (p? x) ...) implies (and ... (q? x) ...))
  ;; each predicate only appears on the left hand side of one rule
  ;; assume partial order, so there should be no cycle
  `([prime? ⇒ nat?]
    [zero? ⇒ even? nat? non-neg? non-pos?]
    [even? odd? ⇒ int?]
    [nat? ⇒ int? non-neg?]
    [neg? ⇒ non-pos? non-zero?]
    [pos? ⇒ non-neg? non-zero?]
    [int? non-pos? non-neg? ⇒ real?]
    [non-zero? ⇒ num?]
    [real? ⇒ num?]
    [num? string? proc? cons? nil? ⇒ true?]
    [false? ⇒ bool?]
    [bool? true? ⇒ any]))

;; rhs : Pred -> [Listof Pred]
;; returns predicates that can be directly implied from given one
(define (rhs name)
  (let loop ([rs rules])
    (match rs
      ['() (error "no rule for " name)]
      [(cons `(,p ... ⇒ ,q ...) rs1)
       (if (member name p) q (loop rs1))])))

;; lhs : Pred -> [SetOf Pred]
;; returns predicates that can directly imply given one
(define (lhs name)
  (foldl (λ (rule lhs)
           (match-let ([`(,p ... ⇒ ,q ...) rule])
             (if (member name q) (append p lhs) lhs)))
         empty rules))

;; implies-what : Pred -> [SetOf Pred]
;; returns predicates that given one can imply
(define implies-what
  (letrec ([cache (make-hash)]
           [memoized
            (λ (op)
              (match (hash-ref cache op '☹)
                ['☹ (let ([result (trace op)])
                      (hash-set! cache op result)
                      result)]
                [result result]))]
           [trace
            (λ (op)
              (match op
                ['any ∅]
                [_ (set-add (apply set-union (map implies-what (rhs op))) op)]))])
    memoized))

;; what-imply : Pred -> [Setof Pred]
;; returns predicates that can imply given one
(define what-imply
  (letrec ([cache (make-hash)]
           [memoized
            (λ (op)
              (match (hash-ref cache op '☹)
                ['☹ (let ([result (trace op)])
                      (hash-set! cache op result)
                      result)]
                [result result]))]
           [trace
            (λ (op)
              (let ([lhs (lhs op)])
                (set-add
                 (if (empty? lhs) ∅
                     (apply set-union (map what-imply lhs)))
                 op)))])
    memoized))

;; TODO: how to factor out memoization? macros?

;; exlucde : Pred -> [Setof Pred]
;; ad-hoc rules for disproving primitive predicates
(define exclude
  (letrec ([rules
            ;; groups of predicates that 'obviously' exclude each other
            ;; hopefully there'll be no cycle
            `([true? false?]
              [num? bool? proc? string? nil? cons?]
              [odd? even?]
              [nat? neg?]
              [zero? pos? neg?]
              [zero? non-zero?]
              [zero? prime?]
              [non-neg? neg?]
              [non-pos? pos?])]
           [others ; i run out of names
            ;; returns all predicates that 'obviously' excludes this one
            (λ (op)
              (foldl (λ (group acc)
                       (let-values ([(me them) (partition (curry equal? op) group)])
                         (if (empty? me) acc
                             (append them acc))))
                     empty rules))]
           [cache (make-hash)]
           [memoized
            (λ (op)
              (match (hash-ref cache op '☹)
                ['☹ (let ([result (trace op)])
                      (hash-set! cache op result)
                      result)]
                [result result]))]
           [trace
            (λ (op)
              (non-det
               what-imply ;; ((p ⇒ ¬q) ∧ (r ⇒ q)) ⇒ (p ⇒ ¬r)
               (set-union
                (list->set (others op))
                (non-det
                 exclude ;; ((p ⇒ q) ∧ (q ⇒ ¬r)) ⇒ (p ⇒ ¬r)
                 (set-subtract (implies-what op) {set op})))))])
    memoized))

;;;; set helper functions

;; s-map : [x -> y] [Setof x] -> [Setof y]
(define (s-map f xs)
  #;(for/set ([x xs]) (f x))
  ; TODO: is this how I use in-set?
  (for/fold ([ys ∅]) ([x (in-set xs)]) (set-add ys (f x))))

;; non-det : (x -> [Setof y]) [Setof x] -> [Setof y]
(define (non-det f xs)
  (if (set-empty? xs) ∅
      (apply set-union (set-map xs f))))