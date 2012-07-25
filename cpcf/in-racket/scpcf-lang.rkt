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
(define FALSE (val #f ∅))
(define BULLET (val '• ∅))

;; contracts
(define c/any `(flat (λ (x) #t)))
(define c/bool `(flat bool?))
(define c/list `(μ (list?) (or/c (flat nil?) (cons/c ,c/any list?))))
(define c/num-list `(μ (num-list?) (or/c (flat nil?) (cons/c (flat num?) num-list?))))
(define c/even-list `(μ (evens?) (or/c (flat nil?) (cons/c (flat even?) evens?))))
(define c/bool-list `(μ (bools?) (or/c (flat nil?) (cons/c (flat bool?) bools?))))

;; mk-contract-cl : Label -> ContractClosure
(define (mk-contract-cl name)
  (contract-cl (flat-c (val name ∅)) ρ0))

;; complement : [OneOf '(num? bool? string? proc? nil? cons?)] -> [Setof ContractClosure]
;; returns set of contracts for complement datatypes
(define complement
  (let ([;; contracts for mutually exclusive partitions of datatypes
         type-partitions (set (mk-contract-cl 'num?)
                              (mk-contract-cl 'bool?)
                              (mk-contract-cl 'string?)
                              (mk-contract-cl 'proc?)
                              (mk-contract-cl 'nil?)
                              (mk-contract-cl 'cons?))])
    (λ (type-pred-name)
      (set-subtract type-partitions (set (mk-contract-cl type-pred-name))))))

;; OpImpl = Label [Listof ValClosure] -> [Setof ANswer]
;; OpRecord = (List (Natural -> Boolean) OpImpl)
;; ops : Symbol ↦ OpImpl ; TODO map to OpRecord
;; primitive ops' implementations
(define ops
  (local
    (;; closures for commonly used values
     [define T {set (exp-cl TRUE ρ0)}]
     [define F {set (exp-cl FALSE ρ0)}]
     [define TF (set-union T F)]
     
     ;; type-pred : Label Exp (Any -> Boolean) -> OpRecord
     [define (type-pred op-name contract prim-test?)
       (λ (l xs)
         (match xs
           [`(,(exp-cl (val u cs) ρ))
            (match u
              ['• (cond
                    [(set-member? cs contract) T]
                    [(set-empty? (set-intersect cs (complement op-name))) TF]
                    [else F])]
              [c (if (prim-test? u) T F)])]
           [`(,clo) F]
           [_ {set (exp-cl (blame/ l op-name) ρ0)}]))] ; arity mismatch
     
     ;; type predicates defined separately for use in several places
     [define t-any? (λ (l xs) T)]
     [define t-num? (type-pred 'num? (mk-contract-cl 'num?) number?)]
     [define t-real? (type-pred 'real? (mk-contract-cl 'real?) real?)]
     [define t-int? (type-pred 'int? (mk-contract-cl 'int?) integer?)]
     [define t-bool? (type-pred 'bool? (mk-contract-cl 'bool?) boolean?)]
     [define t-string? (type-pred 'string? (mk-contract-cl 'string?) string?)]
     [define t-false?
       (λ (l xs)
         (match xs
           [`(,cl)
            (match cl
              [(exp-cl (val u cs) ρ)
               (match u
                 [#f T]
                 ['• (cond
                       [(set-member? cs (mk-contract-cl 'false?)) T]
                       [(set-member? cs (mk-contract-cl 'true?)) F]
                       [(set-empty? (set-intersect cs (set-union (complement 'bool?)))) TF]
                       [else F])]
                 [_ F])]
              [_ F])]
           [_ {set (exp-cl (blame/ l 'false?) ρ0)}]))] ; arity mismatch
     [define t-true?
       (λ (l xs)
         (s-map (λ (r) (match (val-pre (exp-cl-exp r))
                         [#t (close FALSE ρ0)]
                         [#f (close TRUE ρ0)]))
                (t-false? l xs)))]
     [define t-proc?
       (λ (l xs)
         (match xs
           [`(,(exp-cl (val '• cs) ρ))
            (cond
              [(set-member? cs (mk-contract-cl 'proc?)) T]
              [(set-empty? (set-intersect cs (complement 'proc?))) TF]
              [else F])]
           [`(,(exp-cl (val u cs) ρ)) (if (or (lam? u) (op? u)) T F)]
           [`(,(mon-fn-cl h f g c e)) T]
           [`(,cl) F]
           [_ {set (exp-cl (blame/ l 'proc?) ρ0)}]))] ; arity mismatch
     
     
     ;; contract sets defined separately for use in several places
     [define t-num/c {set (mk-contract-cl 'num?)}]
     [define t-real/c (set-add t-num/c (mk-contract-cl 'real?))]
     [define t-int/c (set-add t-real/c (mk-contract-cl 'int?))]
     [define t-bool/c {set (mk-contract-cl 'bool?)}]
     [define t-string/c {set (mk-contract-cl 'string?)}]
     
     ;; concrete? : ValClosure -> Bool
     ;; checks whether a closure represents a concrete value
     (define (concrete? cl)
       (match cl
         [(exp-cl (val u cs) ρ) (not (equal? u '•))]
         [_ #f]))
     
     ;; mk-op : Label [Listof TypePred] [PreVal -> PreVal] [Setof ContractClosure]
     ;;      -> OpImpl
     ;; makes fixed-arity operator on non-pair values
     [define (mk-op name dom-tests prim-op refinements)
       (λ (l xs)
         (let ([dom-oks (map (λ (test x) (test l (list x))) dom-tests xs)])
           (set-union
            (if (ormap (curry subset? F) dom-oks) ; any argument violates
                {set (exp-cl (blame/ l name) ρ0)}
                ∅)
            (if (andmap (curry subset? T) dom-oks) ; exists combination of ok args
                (if (andmap concrete? xs)
                    {set (exp-cl
                          (val
                           (apply prim-op (map (compose val-pre exp-cl-exp) xs))
                           ∅)
                          ρ0)}
                    {set (exp-cl (val '• refinements) ρ0)})
                ∅))))]
     
     ;; cl=? : ValClosure ValClosure -> [Setof Boolean]
     ; TODO rewrite
     [define (cl=? cl1 cl2)
       (match `(,cl1 ,cl2)
         [`(,(cons-cl c1 c2) ,(cons-cl c3 c4))
          (non-det (match-lambda
                     [#t (cl=? c2 c4)]
                     [#f {set #f}])
                   (cl=? c1 c3))]
         [`(,(mon-fn-cl h f g c1 cl1) ,(mon-fn-cl h f g c2 cl2))
          (set-union {set #f} {set (cl=? cl1 cl2)})]
         [`(,(exp-cl (val u1 cs1) ρ1) ,(exp-cl (val u2 cs2) ρ2))
          (if (or (equal? '• u1) (equal? '• u2))
              {set #t #f}
              {set (equal? u1 u2)})]
         [_ {set #f}])])
    
    (hash
     ;; type predicates
     'num? t-num?
     'real? t-real?
     'int? t-int?
     'bool? t-bool?
     'string? t-string?
     'true? t-true?
     'false? t-false?
     'nil? (λ (l xs)
             (match xs
               [`(,(exp-cl (val u cs) ρ))
                (match u
                  ['nil T]
                  ['• (cond
                        [(set-member? cs (mk-contract-cl 'nil?)) T]
                        [(set-empty? (set-intersect cs (complement 'nil?))) TF]
                        [else F])]
                  [_ F])]
               [`(,clo) F]
               [_ {set (exp-cl (blame/ l 'nil?) ρ0)}])) ; arity mismatch
     'cons? (λ (l xs)
              (match xs
                [`(,clo) (s-map (match-lambda
                                  [`(,c1 ,c2) (close TRUE ρ0)]
                                  [_ (close FALSE ρ0)])
                                (split-cons clo))]
                [_ {set (exp-cl (blame/ l 'cons?) ρ0)}])) ; arity mismatch
     'proc? t-proc?
     
     'equal? (λ (l xs)
               (match xs
                 [`(,cl1 ,cl2)
                  (s-map (match-lambda
                           [#t (close TRUE ρ0)]
                           [#f (close FALSE ρ0)])
                         (cl=? cl1 cl2))]
                 [_ {set (exp-cl (blame/ l 'equal?) ρ0)}])) ; arity mismatch
     
     'zero? (mk-op 'zero? `(,t-num?) zero? t-bool/c)
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
     '/ (mk-op '/ `(,t-num? ,t-num?) / t-num/c) ;; TODO: handles div by 0!!
     'mod (mk-op 'mod `(,t-int? ,t-int?) modulo t-int/c) ;; TODO: handles div by 0!!
     'quot (mk-op 'quotient `(,t-int? ,t-int?) quotient t-int/c) ;; TODO: handles div by 0!!
     'gcd (mk-op 'gcd `(,t-int? ,t-int?) gcd t-int/c)
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
                    ; promote (cons/c (•/{...c...}) nil) to (• {...(listof c)...})
                    [`(,(exp-cl (val '• cs1) ρ1) ,(exp-cl (val 'nil cs2) ρ2))
                     (close
                      (val '•
                           (set-add
                            (s-map (λ (cl)
                                     (match-let ([(contract-cl c ρc) cl])
                                       (close-contract
                                        (cons-c c
                                                (rec-c (or-c (flat-c (val 'nil ∅))
                                                             (cons-c (shift-con 1 c)
                                                                     (ref-c 0)))))
                                        ρc)))
                                   cs1)
                            (let ([C/ANY (read-con c/any)])
                              (close-contract
                               (cons-c C/ANY
                                       (rec-c (or-c (flat-c (val 'nil ∅))
                                                    (cons-c C/ANY (ref-c 0)))))
                               ρ0)))) ρ0)]
                    ; promote (cons/c (•/{...c...}) (•/{...(cons c (listof c))...}) to
                    ; (•/{...(cons/c c (listof c)...}
                    [`(,(exp-cl (val '• cs1) ρ1) ,(exp-cl (val '• cs2) ρ2))
                     (let* ([cdr-is-list? #f]
                            [C/ANY (read-con c/any)]
                            [list-contracts
                             (set-subtract
                              (for/set ([c cs2] #|TODO is there any way to pattern match in here?|#)
                                       (match c
                                         [(contract-cl (cons-c c1
                                                               (rec-c (or-c (flat-c (val 'nil ∅))
                                                                            (cons-c c2 (ref-c 0)))))
                                                       ρc)
                                          (if (equal? c2 (shift-con 1 c1))
                                              (begin
                                                (set! cdr-is-list? #t)
                                                (if (set-member? cs1 c1)
                                                    c
                                                    'ignore))
                                              'ignore)]
                                         [_ 'ignore]))
                              (set 'ignore))])
                       (if cdr-is-list?
                           (close (val '• (set-add list-contracts
                                                   (close-contract
                                                    (cons-c C/ANY
                                                            (rec-c (or-c (flat-c (val 'nil ∅))
                                                                         (cons-c C/ANY (ref-c 0)))))
                                                    ρ0)))
                                  ρ0)
                           (cons-cl (first xs) (second xs))))]
                    [`(,c1 ,c2) (cons-cl c1 c2)]
                    [_ (exp-cl (blame/ l 'cons) ρ0)])}) ; arity mismatch
     
     ;; TODO: refactor car and cdr using split-cons
     'car (λ (l xs)
            (match xs
              [`(,clo) (s-map (match-lambda
                                [`(,c1 ,c2) c1]
                                ['() (close (blame/ l 'car) ρ0)])
                              (split-cons clo))]
              [_ {set (exp-cl (blame/ l 'car) ρ0)}])) ; arity mismatch
     'cdr (λ (l xs)
            (match xs
              [`(,clo) (s-map (match-lambda
                                [`(,c1 ,c2) c2]
                                ['() (close (blame/ l 'cdr) ρ0)])
                              (split-cons clo))]
              [_ {set (exp-cl (blame/ l 'cdr) ρ0)}]))))) ; arity mismatch

;; split-cons : ValClosure -> [SetOf [(List ValClosure Closure) or Empty]]
(define (split-cons cl)
  
  ;; accum-cons-c : [Setof ContractClosure] 
  ;;             -> (List [Setof ContractClosure] [Setof ContractClosure]) or ()
  ;; accumulates contracts for pair's car and cdr
  ;; returns () if contracts cannot prove it's a pair
  (define (accum-cons-c cs)
    (for/fold ([acc '()]) ([c (in-set cs)])
      (match-let ([(contract-cl c ρc) c])
        (match c
          [(cons-c c1 c2)
           (match acc
             [`(,cs1 ,cs2) `(,(set-add cs1 (close-contract c1 ρc)) ,(set-add cs2 (close-contract c2 ρc)))]
             [`() `(,(set (close-contract c1 ρc)) ,(set (close-contract c2 ρc)))])]
          [(flat-c (val 'cons? _))
           (match acc
             [`(,cs1 ,cs2) acc]
             ['() `(,∅ ,∅)])]
          [_ acc]))))
  
  (match cl
    ; TODO: case like (cons • •) / {(cons/c (flat even?) (flat odd?))}
    ; maybe turn it to (• / {(flat even?)}) and (• / {(flat odd?)})
    ; instead of currently just • and •
    ; ah, ConsClosure currently does not have a 'dedicated' set of refinements
    ; neither does MonitoredFuncClosure. Do they ever need that?
    [(cons-cl c1 c2) {set `(,c1 ,c2)}]
    [(exp-cl (val '• cs) ρ)
     (match (accum-cons-c cs)
       ; proven abstract pair
       [`(,cs1 ,cs2) {set `(,(close (val '• cs1) ρ0) ,(close (val '• cs2) ρ0))}]
       ; nothing is known
       [`()
        (if (set-empty? (set-intersect cs (complement 'cons?)))
            {set `(,(close BULLET ρ0) ,(close BULLET ρ0)) '()}
            {set '()})])]
    [_ {set '()}])) ; known not a pair

;; δ : Op [Listof ValClosure] Lab -> [Setof Answer]
(define (δ op xs l)
  ((hash-ref ops op) l xs))

;; arity : Op -> Natural
;; TODO: just temporary fix, move all this info to ops table!!
(define (arity o)
  (cond
    [(member o '(num? real? int? bool? string? true? false? nil? cons?
                      proc? zero? even? odd? prime? not sqrt str-len car cdr)) 1]
    [(member o '(+ - * = ≠ < ≤ > ≥ ++ str=? str≠? str<? str≤? str>? str≥? cons)) 2]
    [(member o '(substring)) 3]
    [(error "forgot " o)]))


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
       [_ {set (if (op? u) (= n (arity u)) #f)}])]
    [(mon-fn-cl h f g (contract-cl (func-c cs1 c2) ρc) cl1)
     {set (= n (length cs1))}]
    [_ {set #f}]))

;;;; set helper functions

;; s-map : [x -> y] [Setof x] -> [Setof y]
(define (s-map f xs)
  #;(for/set ([x xs]) (f x))
  ; TODO: is this how I use in-set?
  (for/fold ([ys ∅]) ([x (in-set xs)]) (set-add ys (f x))))

;; non-det : (x -> [Setof y]) [Setof x] -> [Setof y]
(define (non-det f xs)
  (apply set-union (set-map xs f)))