#lang racket
(require redex) ; variable-not-in
(require rackunit)
(require racket/contract)

(require "env.rkt")

(provide
 
 (contract-out
  [struct prog ([modules modls?] [main exp?])]
  [struct modl ([vals hash?] [contracts hash?])]
  
  [struct ref ([distance natural?])]
  [struct val ([pre pre-val?] [refinements (set/c contract-cl?)])]
  
  [struct lam ([arity natural?] [body exp?] [varargs? boolean?])]
  [struct app ([func exp?] [args (listof exp?)] [lab label?])]
  [struct rec ([body exp?])]
  [struct if/ ([test exp?] [then exp?] [else exp?])]
  [struct mon ([orig label?] [pos label?] [neg label?]
                             [con contract/?] [exp exp?])]
  [struct blame/ ([violator label?] [violatee label?])]
  [struct mod-ref ([l label?] [f label?] [m label?])]
  [struct constr ([tag label?] [arity natural?])]
  [struct acc ([tag label?] [idx natural?])]
  [struct constr-check ([tag label?])]
  
  [struct flat-c ([exp exp?])]
  [struct func-c ([dom (listof contract/?)] [rng contract/?] [varargs? boolean?])]
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
                                   [exp val-cl?])]
  [struct cons-cl ([car val-cl?] [cdr val-cl?])]
  [struct struct-cl ([tag label?] [fields (listof val-cl?)])]
  
  [struct contract-cl ([con contract/?] [env env?])]
  [clo? (any/c . -> . boolean?)]
  [close (exp? env? . -> . clo?)]
  [close-contract (contract/? env? . -> . contract-cl?)]
  [val-cl? (any/c . -> . boolean?)]
  
  [shift (natural? exp? . -> . exp?)]
  
  [δ (prim? (listof val-cl?) label? . -> . (set/c clo?))]
  [δ′ (prim? (listof val-cl?) label? . -> . (set/c clo?))]
  [split-cons (val-cl? . -> . (set/c (or/c empty? (list/c val-cl? val-cl?))))]
  
  [read-prog (s-exp? . -> . prog?)]
  #;[show-prog (prog? . -> . s-exp?)]
  [read-exp (s-exp? . -> . exp?)]
  ; for use by havoc
  [read-exp-with (modls? (listof label?) (listof symbol?) symbol? s-exp? . -> . s-exp?)]
  #;[show-exp (exp? . -> . s-exp?)]
  
  [modl-get-defn (modl? label? . -> . exp?)]
  [modl-get-contract (modl? label? . -> . contract/?)]
  [modl-provides? (modl? label? . -> . boolean?)]
  [mod-by-name (modls? label? . -> . modl?)]
  [upd-mod-by-name (modls? label? label? (val? . -> . val?) . -> . modls?)]
  
  [proc-with-arity? (val-cl? natural? . -> . (set/c boolean?))]
  
  [mk-contract-cl (prim? . -> . contract-cl?)]
  
  [contracts-imply? ([set/c contract-cl?] prim? . -> . verified?)]
  [concrete? (val-cl? . -> . boolean?)]
  [proc? (val-cl? . -> . verified?)]
  [approx (val-cl? . -> . val-cl?)]
  [refine ((set/c contract-cl?) contract-cl? . -> . (set/c (set/c contract-cl?)))]
  
  [exp? (any/c . -> . boolean?)]
  [answer? (any/c . -> . boolean?)]
  [pre-val? (any/c . -> . boolean?)]
  [label? (any/c . -> . boolean?)]
  [prim? (any/c . -> . boolean?)]
  [s-exp? (any/c . -> . boolean?)]
  [modls? (any/c . -> . boolean?)])
 
 c/list-of c/non-empty-list-of
 c/any c/bool c/list c/num-list c/real-list c/even-list c/bool-list c/int-list
 
 ;; s-map : [x -> y] [Setof x] -> [Setof y]
 s-map
 
 ;; non-det : (x -> [Setof y]) [Setof x] -> [Setof y]
 non-det
 ∅)

;; Module := (modl [Hashtable Label Exp] [Hashtable Label Contract])
(struct modl (vals contracts) #:transparent)
(define modl-mt (modl (hash) (hash)))

;; modl-add-defn : Module Label Exp -> Module
(define (modl-add-defn m x v)
  (match-let ([(modl vals contracts) m])
    (modl (hash-set vals x v) contracts)))

;; modl-add-contract : Module Label Contract -> Module
(define (modl-add-contract m x c)
  (match-let ([(modl vals contracts) m])
    (modl vals (hash-set contracts x c))))

;; modl-get-defn : Module Label -> Exp
(define (modl-get-defn m x)
  (match (hash-ref (modl-vals m) x '☹)
    ['☹ (error "no definition for" x)]
    [v v]))

;; modl-get-contract : Module Label -> Contract
(define (modl-get-contract m x)
  (match (hash-ref (modl-contracts m) x '☹)
    ['☹ (error "module does not export" x)]
    [c c]))

;; modl-provides? : Module Label -> Boolean
(define (modl-provides? m x)
  (hash-has-key? (modl-contracts m) x))

;; modl-exports? : Module Label -> Bool
(define (modl-exports? m x)
  (hash-has-key? (modl-contracts m) x))

;; Modules = HashTable Label Module
(define modls? hash?)

;; mod-by-name :: Modules Label -> Module
(define (mod-by-name modls name)
  (hash-ref modls name modl-mt))

;; upd-mod-by-name : Modules Label Label [Value -> Value] -> Module
(define (upd-mod-by-name ms m-name x-name f)
  (let ([m (mod-by-name ms m-name)])
    (if (modl-exports? m x-name)
        (hash-set ms m-name (modl-add-defn m x-name (f (modl-get-defn m x-name))))
        ms)))

;; modls-add-defn : Modules Label Label Exp -> Modules
(define (modls-add-defn modls mod-name x v)
  (hash-set modls mod-name
            (modl-add-defn (mod-by-name modls mod-name) x v)))

;; modls-add-contract : Modules Label Label Contract -> Modules
(define (modls-add-contract modls mod-name x c)
  (hash-set modls mod-name
            (modl-add-contract (mod-by-name modls mod-name) x c)))


;; ∅ : Setof x
;; (eq? (set) (set)) = #f, and we have a lot of empty sets around,
;; so I guess this might be useful. It looks nicer anyway.
(define ∅ (set))

;; s-exp? : Any -> Boolean
(define s-exp? any/c) ; TODO

;; Prog := (prog Modules Exp)
(struct prog (modules main) #:transparent)

(struct exp () #:transparent)
(struct answer exp () #:transparent)
;; Val := (val Preval [Listof ContractClosure])
(struct val answer (pre refinements) #:transparent)
;; Ref := (ref Natural)
(struct ref exp (distance) #:transparent)
;; App := (app Exp [Listof Exp] Label)
(struct app exp (func args lab)
  ;; FIXME: this is a temporary hack, until contract becomes first class
  #:methods gen:equal+hash
  [(define (equal-proc a b equal?/rec)
     (and (equal?/rec (app-func a) (app-func b))
          (= (length (app-args a)) (length (app-args b)))
          (andmap equal?/rec (app-args a) (app-args b))))
   (define (hash-proc x hash/rec)
     (+ (* 41 (hash/rec (app-func x)))
        (hash/rec (app-args x))))
   (define (hash2-proc x hash/rec)
     (+ (hash/rec (app-func x))
        (* 41 (hash/rec (app-args x)))))]
  #:transparent)
;; Rec := (rec Exp)
(struct rec exp (body) #:transparent)
;; If := (if/ Exp Exp Exp)
(struct if/ exp (test then else) #:transparent)
;; Mon := (mon Label Label label Contract Exp)
(struct mon exp (orig pos neg con exp) #:transparent)
;; ModRef := (mod-ref Label Label Label)
(struct mod-ref exp (l f m)
  ;; FIXME: temporary hack??
  #:methods gen:equal+hash
  [(define (equal-proc a b equal?/rec)
     (and (equal?/rec (mod-ref-l a) (mod-ref-l b))
          (equal?/rec (mod-ref-f a) (mod-ref-f b))))
   (define (hash-proc x hash/rec)
     (+ (* 41 (hash/rec (mod-ref-l x)))
        (hash/rec (mod-ref-f x))))
   (define (hash2-proc x hash/rec)
     (+ (hash/rec (mod-ref-l x))
        (* 41 (hash/rec (mod-ref-f x)))))]
  #:transparent) ; reference to f in l from m

;; Blame := (blame/ Label Label)
(struct blame/ answer (violator violatee) #:transparent)

;; PreVal := • | Number | Boolean | String | Lambda | Nil
(define (pre-val? x)
  (or (eq? x '•) (number? x) (boolean? x) (string? x) (lam? x) (eq? 'nil x) (prim? x)
      (constr? x) (acc? x) (constr-check? x)))
;; Constructor := (constr Label Nat)
(struct constr (tag arity) #:transparent)
;; Accessor := (acc Label Nat)
(struct acc (tag idx) #:transparent)
;; Type-Pred := (constr-check Label)
(struct constr-check (tag) #:transparent)
;; Lambda := (lam Natural Exp Boolean)
(struct lam (arity body varargs?) #:transparent)

;; Closure := ExpClosure | MonFnClosure | ConsClosure
(struct clo () #:transparent)
;; ExpClosure := (exp-cl Exp Env)
(struct exp-cl clo (exp env) #:transparent)
;; MonFnClosure := (mon-fn-cl Label Label Label ContractClosure Closure)
(struct mon-fn-cl clo (orig pos neg con exp) #:transparent)
;; ConsClosure := (cons-cl Closure Closure)
(struct cons-cl clo (car cdr) #:transparent)
;; StructClosure := (struct-cl Label [Listof Closure])
(struct struct-cl clo (tag fields) #:transparent)

;; close : Exp Env -> Closure
;; closes expression with given environment, dropping all unused closures
(define (close exp en)
  (exp-cl exp (env-restrict (free-vars exp) en)))

;; val-cl? : Closure -> Boolean
;; checks whether closure represents a value
(define (val-cl? clo)
  (or (and (exp-cl? clo) (val? (exp-cl-exp clo)))
      (mon-fn-cl? clo)
      (cons-cl? clo)
      (struct-cl? clo)))

;; checks whether symbol names a primitive op
(define (prim? o)
  (hash-has-key? ops o))

;; label? : Any -> Boolean
(define label? symbol?)

;; Contract := FlatContract | FuncContract | ConsContract
;;           | OrContract | AndContract | RecContract
(struct contract/ () #:transparent)
(struct flat-c contract/ (exp) #:transparent)
(struct func-c contract/ (dom rng varargs?) #:transparent)
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
(define (c/list-of c)
  `(μ (pred) (or/c (flat nil?) (cons/c ,c pred))))
(define (c/non-empty-list-of c)
  `(cons/c ,c ,(c/list-of c)))
(define c/any `(flat (λ (x) #t)))
(define c/bool `(flat bool?))
(define c/list (c/list-of '(flat (λ (x) #t))))
(define c/num-list (c/list-of '(flat num?)))
(define c/int-list (c/list-of '(flat int?)))
(define c/real-list (c/list-of '(flat real?)))
(define c/even-list (c/list-of '(flat even?)))
(define c/bool-list (c/list-of '(flat bool?)))

;; mk-contract-cl : Pred -> ContractClosure
;; makes contract out of primitive predicate
(define mk-contract-cl
  (let ([cache (make-hash)])
    (λ (name) ; memoized
      (match (hash-ref cache name '☹)
        ['☹ (let ([r (contract-cl (flat-c (val name ∅)) ρ0)])
              (hash-set! cache name r)
              r)]
        [r r]))))

;; Op := (op (Nat -> Bool) (Lab [Listof ValClosure] -> [Setof ValClosure])
(struct op (arity proc))

;; Verified := Proved|Refuted|Neither
(define (verified? x)
  (or (equal? 'Proved x) (equal? 'Refuted x) (equal? 'Neither x)))

;; contracts-imply? : [Setof ContractClosure] [TreeOf Pred] -> Verified
;; checks whether set of refinements is enough to prove or refute given
;; primitive predicate(s)
(define (contracts-imply? cs p)
  (if (cons? p) ; is (list? p) more expensive?
      
      ; on list of all predicates to prove
      ; TODO: write manual loop for short-circuit behavior?
      (let ([rs (map (curry contracts-imply? cs) p)])
        (cond
          [(ormap (curry equal? 'Refuted) rs) 'Refuted]
          [(andmap (curry equal? 'Proved) rs) 'Proved]
          [else 'Neither]))
      
      ; on single predicate
      (local ([define excludes (exclude p)]
              [define proves (what-imply p)]
              [define (on-contract acc c)
                (match acc
                  ['Refuted 'Refuted]
                  [_ (match c
                       [(contract-cl (flat-c (val q cs1)) ρc)
                        (cond
                          [(set-member? excludes q) 'Refuted]
                          [(set-member? proves q) 'Proved]
                          [else acc])]
                       [(contract-cl (cons-c c1 c2) ρc)
                        ; relies on 'cons? having no predicate that implies it
                        (if (set-member? (implies-what 'cons?) p) 'Proved 'Refuted)]
                       [(contract-cl (func-c cs1 c2 _) ρc)
                        ; relies on 'proc? having no predicate that implies it
                        (if (set-member? (implies-what 'proc?) p) 'Proved 'Refuted)]
                       [(contract-cl (or-c c1 c2) ρc)
                        (match (on-contract acc (close-contract c1 ρc))
                          ['Refuted (on-contract acc (close-contract c2 ρc))]
                          ['Proved 'Proved]
                          ['Neither (match (on-contract acc (close-contract c2 ρc))
                                      ['Refuted 'Neither]
                                      [r r])])]
                       [(contract-cl (rec-c c1) ρc)
                        ; TODO potential infinite loop?
                        (on-contract acc (close-contract c1 (env-extend c ρc)))]
                       [(contract-cl (and-c c1 c2) ρc)
                        (on-contract (on-contract acc (close-contract c1 ρc)) (close-contract c2 ρc))]
                       [(contract-cl (ref-c x) ρc) (on-contract acc (env-get x ρc))]
                       [_ acc])])])
        
        (for/fold ([acc 'Neither]) ([c (in-set cs)])
          (on-contract acc c)))))

;; proc? : ValClosure -> Verified
;; checks whether closure represents a function
(define proc?
  (match-lambda
    [(exp-cl (val '• cs) ρ) (contracts-imply? cs 'proc?)]
    [(exp-cl (val u cs) ρ)
     (if (or [lam? u] [constr? u] [acc? u] [constr-check? u] [prim? u])
         'Proved 'Refuted)]
    [(mon-fn-cl h f g c cl) 'Proved]
    [_ 'Refuted]))

;; concrete? : ValClosure -> Bool
;; checks whether a closure represents a concrete value
(define (concrete? cl)
  (match cl
    [(exp-cl (val u cs) ρ) (not (equal? u '•))]
    [(mon-fn-cl h f g c v) (concrete? v)]
    [(cons-cl c1 c2) (and (concrete? c1) (concrete? c2))]
    [(struct-cl _ xs) (andmap concrete? xs)]))

;; entries-prim-pred : Listof (List Symbol (PreVal -> Boolean))
;; predicates on primitive data
[define entries-prim-pred
  `([prime? ,(and/c number? (λ (x) (if (member x '(2 3 5 7)) #t #f)))]
    [zero? ,(and/c number? zero?)]
    [nat? ,(and/c integer? (or/c positive? zero?))]
    [even? ,(and/c integer? even?)]
    [odd? ,(and/c integer? odd?)]
    [non-neg? ,(and/c real? (not/c negative?))]
    [non-pos? ,(and/c real? (not/c positive?))]
    [non-zero? ,(and/c number? (not/c zero?))]
    [pos? ,(and/c real? positive?)]
    [neg? ,(and/c real? negative?)]
    [int? ,integer?]
    [real? ,real?]
    [num? ,number?]
    [string? ,string?]
    [nil? ,(curry equal? 'nil)]
    [false? ,false?]
    [not ,false?]
    [bool? ,boolean?])]

; prim-preds : [Listof Symbol]
(define prim-preds
  (map first entries-prim-pred))

;; prim-check : [TreeOf Pred] Preval -> Boolean
;; checks whether primitive value satisfy predicate with given name
(define (prim-check p pre-val)
  (if (cons? p)
      (andmap (λ (q) (prim-check q pre-val)) p)
      (match-let ([(cons (list nm o) _)
                   (memf (compose (curry equal? p) first) entries-prim-pred)])
        (o pre-val))))

;; approx-contracts : ValExpClosure -> [Setof ContractClosure]
(define approx-contracts
  (let ([satisfying-contracts
         (λ (u)
           (set-add
            (foldl (λ (pred acc)
                     (if (prim-check pred u) (set-add acc (mk-contract-cl pred)) acc))
                   ∅ prim-preds)
            ; treat true? separately
            (mk-contract-cl (if (false? u) 'false? 'true?))))])
    (match-lambda
      [(exp-cl (val (lam n e _) cs) ρ) (set-union cs (mk-contract-cl 'proc?))]
      [(exp-cl (val '• cs) ρ) cs]
      [(exp-cl (val u cs) ρ) (set-union cs (satisfying-contracts u))])))

;; approx : ValClosure -> ValClosure
(define (approx x)
  
  ;; mk-func-c : Natural Boolean -> FuncContractClosure
  ;; returns contract for function of given arity
  (define (mk-func-c n var?)
    (define C/ANY (read-con c/any))
    (close-contract (func-c (make-list n C/ANY) C/ANY var?) ρ0))
  
  ;; abs-cons : ValClosure ValClosure -> ValClosure
  (define (abs-cons c1 c2)
    (define C/NIL (flat-c (val 'nil? ∅)))
    (define C/ANY (read-con c/any))
    (define (mk-c/non-empty-list-of c ρc)
      (close-contract
       (cons-c c
               (rec-c (or-c C/NIL
                            (cons-c (shift-con 1 c) (ref-c 0)))))
       ρc))
    (define C/NON-MT-LIST (mk-c/non-empty-list-of C/ANY ρ0))
    (define CONS-•-• (cons-cl (close BULLET ρ0) (close BULLET ρ0)))
    (match `(,c1 ,c2)
      [`(,(exp-cl (val '• cs1) ρ1) ,(exp-cl (val '• cs2) ρ2))
       (cond
         ; cdr is nil, approx (cons X nil) to (non-empty-list-of X)
         [(set-member? cs2 (mk-contract-cl 'nil?))
          (close
           (val '•
                (set-add
                 (s-map (match-lambda
                          [(contract-cl c ρc) (mk-c/non-empty-list-of c ρc)])
                        cs1)
                 C/NON-MT-LIST))
           ρ0)]
         ; if cdr is (non-empty-list-of Y)ch 
         ; approx (cons X (non-empty-list-of Y)) to (non-empty-list-of (X ∩ Y))
         [else
          (let* ([cdr-is-list? #f]
                 [IGNORE (void)]
                 [list-contracts
                  (set-remove
                   (for/set
                    ([c cs2])
                    (match c
                      [(contract-cl (cons-c c1
                                            (rec-c (or-c (flat-c (val 'nil? ∅))
                                                         (cons-c c2 (ref-c 0)))))
                                    ρc)
                       (when (equal? c2 (shift-con 1 c1))
                         [set! cdr-is-list? #t]
                         [when (set-member? cs1 (close-contract c1 ρc)) c])]
                      [(contract-cl (cons-c c1 (ref-c x)) ρc)
                       (match (env-get x ρc)
                         [(contract-cl (rec-c (or-c (flat-c (val 'nil? ∅))
                                                    (cons-c c2 (ref-c 0))))
                                       ρc2)
                          (when (equal? c2 (shift-con 1 c1))
                            [set! cdr-is-list? #t]
                            [when (set-member? cs1 (close-contract c1 ρc)) c])]
                         [_ IGNORE])]
                      [_ IGNORE]))
                   IGNORE)])
            (if cdr-is-list?
                (close (val '• (set-add list-contracts C/NON-MT-LIST)) ρ0)
                CONS-•-•))])]
      [_ CONS-•-•])
    
    )
  
  (match x
    [(exp-cl (val (lam n e vargs?) cs) ρ)
     (close (val '• (set-add cs (mk-func-c n vargs?))) ρ0)]
    [(exp-cl (val (constr tag n) cs) ρ)
     (close (val '• (set-add cs (mk-func-c n #f))) ρ0)]
    [(exp-cl (val (acc tag i) cs) ρ)
     (close (val '• (set-add cs (mk-func-c 1 #f))) ρ0)]
    [(exp-cl (val (constr-check tag) cs) ρ)
     (close (val '• (set-add cs (mk-func-c 1 #f))) ρ0)]
    [(exp-cl _ ρ) (close (val '• (approx-contracts x)) ρ0)]
    [(mon-fn-cl h f g c v) (mon-fn-cl h f g c (approx v))]
    [(cons-cl c1 c2)
     (abs-cons (approx c1) (approx c2))]
    [(struct-cl tag xs) (error "TODO")]))

;; ops : Symbol -> OpImpl
(define ops
  (local
    (;; closures for commonly used values
     [define T {set CL-TRUE}]
     [define F {set CL-FALSE}]
     [define TF (set-union T F)]
     
     ;; entries-prim-op : Listof (List Symbol (ListOf ((TreeOf Pred)* → Pred)) (PreVal* → PreVal))
     ;; operators on primitive data
     ;; IMPORTANT:
     ;; * the first contract must be a catch-all one; the other ones don't matter
     ;; * try to make range as specific as possible, while domains as general as possible
     (define entries-prim-op
       `([+ ([num? num? → num?]
             [real? real? → real?]
             [zero? zero? → zero?]
             [nat? nat? → nat?]
             ; the even/odd things are just for fun, not sure if these are practical
             [even? even? → even?]
             [odd? odd? → even?]
             [even? odd? → odd?]
             [odd? even? → odd?]
             [int? int? → int?]
             [pos? non-neg? → pos?]
             [non-neg? pos? → pos?]
             [neg? non-pos? → neg?]
             [non-pos? neg? → neg?]
             [non-pos? non-pos? → non-pos?]
             [non-neg? non-neg? → non-neg?])
            ,+]
         [- ([num? num? → num?]
             [real? real? → real?]
             [zero? zero? → zero?]
             [even? even? → even?]
             [odd? odd? → even?]
             [even? odd? → odd?]
             [odd? even? → odd?]
             [int? int? → int?])
            ,-]
         [* ([num? num? → num?]
             [real? real? → real?]
             [zero? num? → zero?]
             [num? zero? → zero?]
             [nat? nat? → nat?]
             [even? int? → even?]
             [int? even? → even?]
             [odd? odd? → odd?]
             [int? int? → int?])
            ,*]
         [/ ([num? non-zero? → num?]
             [real? (non-zero? real?) → real?]) ,/]
         [mod ([int? (int? non-zero?) → int?]) ,modulo]
         [quot ([int? (int? non-zero?) → int?]) ,quotient]
         [sqrt ([num? → num?]
                [zero? → zero?]
                [pos? → pos?]
                [non-neg? → non-neg?])
               ,sqrt]
         [gcd ([int? int? → int?]) ,gcd]
         [add1 ([num? → num?]
                [nat? → nat?]
                [int? → int?]
                [real? → real?]
                [odd? → even?]
                [even? → odd?]
                [zero? → pos?])
               ,add1]
         [sub1 ([num? → num?]
                [int? → int?]
                [real? → real?]
                [odd? → even?]
                [even? → odd?]
                [zero? → neg?])
               ,sub1]
         [round ([num? → int?]
                 [non-neg? → non-neg?]
                 [non-pos? → non-pos?]
                 [zero? → zero?])
                ,round]
         [ceiling ([num? → int?]) ,ceiling]
         [truncate ([num? → int?]) ,truncate]
         
         [expt ([num? num? → num?]) ,expt]
         [exp ([num? → num?]) ,exp]
         [log ([non-zero? → num?]
               [pos? → real?])
              ,log]
         [sin ([num? → num?]
               [real? → real?])
              ,sin]
         [cos ([num? → num?]
               [real? → real?])
              ,cos]
         [real-part ([num? → real?]) ,real-part]
         [imag-part ([num? → real?]
                     [real? → zero?])
                    ,imag-part]
         [make-polar ([real? real? → num?]) ,make-polar]
         [make-rect ([real? real? → num?]) ,make-rectangular]
         [magnitude ([num? → non-neg?]) ,magnitude]
         [angle ([num? → real?]) ,angle]
         
         [num->string ([num? → string?]) ,number->string]
         [string->number ([string? → num?]) ,string->number]
         
         [string-upcase ([string? → string?]) ,string-upcase]
         [string-downcase ([string? → string?]) ,string-downcase]
         [string-titlecase ([string? → string?]) ,string-titlecase]
         [string-foldcase ([string? → string?]) ,string-foldcase]
         [string-trim ([string? → string?]) ,string-trim]
         
         ;; TODO: maybe improve precision?
         [= ([num? num? → bool?]) ,=]
         [≠ ([num? num? → bool?]) ,(compose not =)]
         [< ([real? real? → bool?]) ,<]
         [≤ ([real? real? → bool?]) ,<=]
         [> ([real? real? → bool?]) ,>]
         [≥ ([real? real? → bool?]) ,>=]
         
         [++ ([string? string? → string?]) ,string-append]
         [str=? ([string? string? → bool?]) ,string=?]
         [str≠? ([string? string? → bool?]) ,(compose not string=?)]
         [str<? ([string? string? → bool?]) ,string<?]
         [str≤? ([string? string? → bool?]) ,string<=?]
         [str>? ([string? string? → bool?]) ,string>?]
         [str≥? ([string? string? → bool?]) ,string>=?]
         [str-len ([string? → nat?]) ,string-length]))
     
     ;; try-rule : `(,p ... → ,q) [Listof [Setof Contract]] -> Verified
     (define (try-rule rule cs)
       (match-let* ([`(,p ... → ,q) rule]
                    [rs (map contracts-imply? cs p)])
         (cond
           [(ormap (curry equal? 'Refuted) rs) 'Refuted]
           [(andmap (curry equal? 'Proved) rs) 'Proved]
           [else 'Neither])))
     
     
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
         [_ {set #f}]
         [`(,(struct-cl t1 xs) ,(struct-cl t2 ys))
          (if (not (equal? t1 t2))
              {set #f}
              (let ([rs (map cl=? xs ys)])
                (set-union
                 (if (ormap (λ (s) (set-member? #f s)) rs) {set #f} ∅)
                 (if (andmap (λ (s) (set-member? #t s)) rs) {set #t} ∅))))])])
    
    (begin
      ;; INITIALIZING
      (define tb (make-hash))
      
      ;; add primitive predicates on primitive data
      (for-each (match-lambda
                  [`(,name ,impl)
                   (hash-set! tb name
                              (op
                               1
                               [λ (_ xs)
                                 (match-let ([`(,cl) xs])
                                   (match cl
                                     [(exp-cl (val '• cs) ρ)
                                      (match (contracts-imply? cs name)
                                        ['Refuted F]
                                        ['Proved T]
                                        ['Neither TF])]
                                     [(exp-cl (val u cs) ρ) (if (impl u) T F)]
                                     [_ F]))]))])
                entries-prim-pred)
      
      ;; add primitive predicates on compound data
      (hash-set! tb 'cons?
                 (op
                  1
                  [λ (_ xs)
                    (match xs
                      [`(,cl) (s-map (match-lambda
                                       [`(,c1 ,c2) CL-TRUE]
                                       [_ CL-FALSE])
                                     (split-cons cl))])]))
      (hash-set! tb 'proc?
                 (op
                  1
                  [λ (_ xs)
                    (match-let ([`(,cl) xs])
                      (match (proc? cl)
                        ['Proved T]
                        ['Refuted F]
                        ['Neither TF]))]))
      (hash-set! tb 'true?
                 (op
                  1
                  [λ (_ xs)
                    (s-map (match-lambda
                             [(exp-cl (val #f cs) ρ) CL-TRUE]
                             [_ CL-FALSE])
                           (δ 'false? xs '†))]))
      
      ;; add primitive ops on primitive data
      (for-each
       (match-lambda
         [`(,name (,contracts ...) ,impl)
          (hash-set!
           tb name
           (op
            (- (length (first contracts)) 2)
            [λ (l xs) ; assume (length xs) matches arity
              (if (andmap exp-cl? xs)
                  (if (andmap concrete? xs)
                      ; check against most generic contract, then apply primitive impl
                      (match-let ([`(,p ... → ,q) (first contracts)]
                                  [zs (map (compose val-pre exp-cl-exp) xs)])
                        {set (close
                              (if (andmap prim-check p zs)
                                  (val (apply impl zs) ∅)
                                  (blame/ l name))
                              ρ0)})
                      ; approximate all arguments then return symbolic result as accurate
                      ; as possible
                      (match-let* ([zs (map approx-contracts xs)]
                                   [(cons r0 rs) contracts])
                        (match (try-rule r0 zs)
                          ; if the catch-all one fails to prove (positively),
                          ; don't bother the other ones
                          ['Refuted {set (close (blame/ l name) ρ0)}]
                          ['Neither {set (close (blame/ l name) ρ0)
                                         (close (val '• {set (mk-contract-cl (last r0))}) ρ0)}]
                          ['Proved
                           (let ([res
                                  (for/fold ([res {set (mk-contract-cl (last r0))}]) ([r rs])
                                    (match (try-rule r zs)
                                      ['Proved (set-add res (mk-contract-cl (last r)))]
                                      [_ res]))])
                             {set (close (val '• res) ρ0)})])))
                  {set (close (blame/ l name) ρ0)})]))])
       entries-prim-op)
      
      ;; ops on primitive data that don't quite 'fit' into the framework
      (hash-set! tb 'substring
                 (op
                  3
                  [λ (l xs)
                    (match xs
                      [`(,s ,i_0 ,i_n)
                       (if (andmap exp-cl? xs)
                           (if (andmap concrete? xs)
                               (match-let ([(exp-cl (val s cs1) ρ1) s]
                                           [(exp-cl (val i_0 cs2) ρ2) i_0]
                                           [(exp-cl (val i_n cs3) ρ3) i_n])
                                 (if (and (string? s) (natural? i_0) (natural? i_n)
                                          (<= i_0 i_n (string-length s)))
                                     {set (close (val (substring s i_0 i_n) ∅) ρ0)}
                                     {set (close (blame/ l 'substring) ρ0)}))
                               (match-let* ([`(,cs1 ,cs2 ,cs3) (map approx-contracts xs)]
                                            [r1 (contracts-imply? cs1 'string?)]
                                            [r2 (contracts-imply? cs2 'nat?)]
                                            [r3 (contracts-imply? cs3 'nat?)])
                                 (if (or (equal? 'Refuted r1) (equal? 'Refuted r2) (equal? 'Refuted r3))
                                     {set (close (blame/ l 'substring) ρ0)}
                                     {set (close (val '• {set (mk-contract-cl 'string?)}) ρ0)
                                          (close (blame/ l 'substring) ρ0)})))
                           
                           {set (close (blame/ l 'substring) ρ0)})])]))
      
      ;; primitive ops on compound data, too complicated to fit into 'framework'
      (hash-set! tb 'cons
                 (op
                  2
                  (λ (l xs)
                    {set (match-let ([`(,c1 ,c2) xs])
                           (cons-cl c1 c2))})))
      
      (hash-set! tb 'car
                 (op
                  1
                  [λ (l xs)
                    (s-map (match-lambda
                             [`(,c1 ,c2) c1]
                             ['() (close (blame/ l 'car) ρ0)])
                           (split-cons (first xs)))]))
      (hash-set! tb 'cdr
                 (op
                  1
                  [λ (l xs)
                    (s-map (match-lambda
                             [`(,c1 ,c2) c2]
                             ['() (close (blame/ l 'cdr) ρ0)])
                           (split-cons (first xs)))]))
      
      (hash-set! tb 'equal?
                 (op
                  2
                  [λ (l xs)
                    (match-let ([`(,cl1 ,cl2) xs])
                      (s-map (match-lambda
                               [#t CL-TRUE]
                               [#f CL-FALSE])
                             (cl=? cl1 cl2)))]))
      
      tb)))

;; split-cons : ValClosure -> [SetOf [(List ValClosure Closure) or Empty]]
(define (split-cons cl)
  
  ;; accum-cons-c : [Setof ContractClosure] 
  ;;             -> [Setof (List [Setof ContractClosure] [Setof ContractClosure])]
  ;; accumulates contracts for pair's car and cdr
  ;; returns () if contracts cannot prove it's a pair
  (define (accum-cons-c cs)
    
    ;; recursively explore contract for possibility of proving/refuting 'cons?
    (define (on-contract acc c)
      (match acc
        ['Refuted 'Refuted]
        [_ 
         (match c
           [(contract-cl (cons-c c1 c2) ρc)
            (non-det
             (match-lambda
               [`(,cs1 ,cs2)
                (for*/set ([cs1′ (refine cs1 (close-contract c1 ρc))]
                           [cs2′ (refine cs2 (close-contract c2 ρc))])
                          `(,cs1′ ,cs2′))]
               ['() ∅])
             (if (set-empty? acc) {set `(,∅ ,∅)} acc))]
           [(contract-cl (flat-c (val p _)) ρc)
            (cond
              [(set-member? (exclude 'cons?) p) 'Refuted]
              [(set-member? (what-imply 'cons?) p)
               (if (set-empty? acc) {set `(,∅ ,∅)} acc)]
              [else acc])]
           [(contract-cl (func-c cs1 cs _) ρc) 'Refuted]
           [(contract-cl (and-c c1 c2) ρc)
            (on-contract (on-contract acc (close-contract c1 ρc)) (close-contract c2 ρc))]
           [(contract-cl (or-c c1 c2) ρc)
            (let ([cs1s (on-contract acc (close-contract c1 ρc))]
                  [cs2s (on-contract acc (close-contract c2 ρc))])
              (match `(,cs1s ,cs2s)
                [`(Refuted Refuted) 'Refuted]
                [`(Refuted ,cs) (set-add cs '())]
                [`(,cs Refuted) (set-add cs '())]
                [_ (set-union cs1s cs2s)]))]
           ; TODO: potential infinite loop?
           [(contract-cl (rec-c c1) ρc)
            (on-contract acc (close-contract c1 (env-extend c ρc)))]
           [(contract-cl (ref-c x) ρc) (on-contract acc (env-get x ρc))]
           [_ acc])]))
    
    (for/fold ([acc ∅]) ([c (in-set cs)])
      (on-contract acc c)))
  
  ;; TODO refactor
  ;; abs-val : [Setof ContractClosure] -> Closure
  (define (abs-val cs)
    (if (= 1 (set-count cs))
        (match (first (set->list cs))
          [(or (contract-cl (flat-c (val (lam 1 (app (val 'equal? ∅) (list (ref 0) v) _) #f) cs)) ρc)
               (contract-cl (flat-c (val (lam 1 (app (val 'equal? ∅) (list v (ref 0)) _) #f) cs)) ρc))
           (close v ρc)]
          [_ (close (val '• cs) ρ0)])
        (close (val '• cs) ρ0)))
  
  
  (match cl
    [(cons-cl c1 c2) {set `(,c1 ,c2)}] ; concrete pair
    [(exp-cl (val '• cs) ρ)
     (match (accum-cons-c cs)
       ['Refuted {set '()}]
       [s (if (set-empty? s)
              ; nothing is known
              {set '() `(,CL-BULLET ,CL-BULLET)}
              ; proved abstract pair
              (s-map (match-lambda
                       [`(,cs1 ,cs2) `(,(abs-val cs1) ,(abs-val cs2))]
                       ['() '()])
                     s))])]
    [_ {set '()}])) ; known not a pair

;; δ, δ′ : Op [Listof ValClosure] Lab -> [Setof Answer]
(define (δ op xs l)
  (match op
    [(constr tag n)
     {set (if (= n  (length xs))
              (struct-cl tag xs)
              (close (blame/ l tag #|TODO|#) ρ0))}]
    [(acc tag i)
     (match xs
       [`(,x) (error "TODO")]
       [_ {set (close (blame/ l tag #|TODO|#) ρ0)}])]
    [(constr-check tag)
     (match xs
       [`(,x) (error "TODO")]
       [_ {set (close (blame/ l tag #|TODO|#) ρ0)}])]
    [_ (let ([o (hash-ref ops op)])
         (if (= (op-arity o) (length xs))
             ((op-proc o) l xs)
             {set (close (blame/ l op) ρ0)}))]))
(define (δ′ op xs l)
  (match op
    [(or 'false? 'true?) (δ op xs l)]
    [_  (s-map
         (λ (a)
           (match a
             [(exp-cl (blame/ f g) _) a]
             [v (approx v)]))
         (δ op xs l))]))

;; free-vars : Exp -> [Setof Natural]
(define (free-vars e)
  (vars≥ 0 e))
;; vars≥ : Exp -> [Setof Natural]
(define (vars≥ d e)
  (match e
    [(ref k) (if (>= k d) {set (- k d)} ∅)]
    [(val u cs) (match u
                  [(lam n b _) (vars≥ (+ n d) b)]
                  [else ∅])]
    [(blame/ l1 l2) ∅]
    [(app f xs l) (set-union (vars≥ d f)
                             (if (empty? xs) ∅
                                 ; why doesn't set-union handle 0 arg?
                                 (apply set-union (map (curry vars≥ d) xs))))]
    [(rec b) (vars≥ (+ 1 d) b)]
    [(if/ e1 e2 e3) (set-union (vars≥ d e1) (vars≥ d e2) (vars≥ d e3))]
    [(mon h f g c e) (set-union (con-vars≥ d c) (vars≥ d e))]
    [(mod-ref f l m) ∅]))
;; con-free-vars : Contract -> [Setof Natural]
(define (con-free-vars c)
  (con-vars≥ 0 c))
;; con-vars≥ : Natural Contract -> [Setof Natural]
(define (con-vars≥ d c)
  (match c
    [(flat-c e) (vars≥ d e)]
    [(func-c cs1 c2 _) (set-union (apply set-union (cons ∅ (map (curry con-vars≥ d) cs1)))
                                  (con-vars≥ (+ (length cs1) d) c2))]
    [(cons-c c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(or-c c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(and-c c1 c2) (set-union (con-vars≥ d c1) (con-vars≥ d c2))]
    [(rec-c c) (con-vars≥ (+ 1 d) c)]
    [(ref-c x) (if (>= x d) {set (- x d)} ∅)]))

;; read-prog : S-exp -> Prog
(define read-prog
  (match-lambda
    [`(,m ... (require ,r ...) ,e)
     (match-let ([modls (read-modls m)])
       (prog modls (read-exp-with modls r '() '† e)))]
    [`(,m ... ,e) (read-prog `(,@ m (require) ,e))]
    [p (error "invalid program form: " p)]))

;; read-modls : [Listof S-exp] -> Modules
(define (read-modls ms)
  
  (define (accessor-name tag field)
    (string->symbol (string-append (symbol->string tag) "-" (symbol->string field))))
  (define (predicate-name tag)
    (string->symbol (string-append (symbol->string tag) "?")))
  
  ;; acc-provides : S-exp Modules -> Modules
  (define (acc-provides m modls)
    (match m
      [`(module ,name
          (provide ,decl ...)
          (require ,req ...)
          ,def ...)
       (let ([acc-decl
              (λ (dec modls)
                (match-let ([`(,x ,_) dec])
                  (modls-add-contract modls name x 'dummy)))])
         (foldl acc-decl modls decl))]
      [`(module ,name
          (provide ,decl ...)
          ,def ...)
       (acc-provides `(module ,name (provide ,@ decl) (require) ,@ def) modls)]))
  
  ;; acc-contracts : S-exp Modules -> Modules
  (define (acc-contracts m modls)
    (match m
      [`(module ,name
          (provide ,decl ...)
          (require ,req ...)
          ,def ...)
       (let ([acc-contract
              (λ (dec modls)
                (match-let ([`(,x ,c) dec])
                  ; Modules [Listof Symbol] [Listof Symbol] Label S-exp -> Contract
                  (modls-add-contract modls name x (read-con-with modls req '() name c))))])
         (foldl acc-contract modls decl))]
      [`(module ,name
          (provide ,decl ...)
          ,def ...)
       (acc-contracts `(module ,name (provide ,@ decl) (require) ,@ def) modls)]))
  
  ;; acc-defns : S-exp Modules -> Modules
  (define (acc-defns m modls)
    (match m
      [`(module ,name
          (provide ,decl ...)
          (require ,req ...)
          ,defn ...)
       (letrec ([acc-defn
                 (λ (def modls)
                   (match def
                     [`(define (,f ,x ...) ,e) (acc-defn `(define ,f (λ ,x ,e)) modls)]
                     [`(define ,x ,e)
                      (modls-add-defn modls name x
                                      (read-exp-with modls req '() name e))]
                     [`(struct ,tag ,fields)
                      (let* ([ms1
                              ; add constructor
                              (modls-add-defn modls name tag
                                              (val (constr tag (length fields)) ∅))]
                             [ms2
                              ; add accessors
                              (for/fold ([ms ms1]) ([field fields]
                                                    [idx (build-list (length fields) identity)])
                                (modls-add-defn ms name (accessor-name tag field)
                                                (val (acc tag idx) ∅)))]
                             [ms3
                              ; add predicate
                              (modls-add-defn ms2 name (predicate-name tag)
                                              (val (constr-check tag) ∅))])
                        ms3)]
                     ))])
         (foldl acc-defn modls defn))]
      [`(module ,name
          (provide ,decl ...)
          ,defn ...)
       (acc-defns `(module ,name (provide ,@ decl) (require) ,@ defn) modls)]))
  ;; FIXME: contracts do not have access to required modules. Another pass?
  (foldl acc-defns (foldl acc-contracts (foldl acc-provides (hash) ms) ms) ms))

;; read-exp : S-exp -> Exp
(define (read-exp s)
  (read-exp-with (hash) '() '() '† s))

;; read-con : S-exp -> Contract
(define (read-con s)
  (read-con-with (hash) '() '() '† s))

;; desugar-one-of : [Listof S-exp] -> S-Exp
(define desugar-one-of
  (match-lambda
    [`(,v) `(flat (λ (x) (equal? x ,v)))]
    [`(,v1 ,v ...) `(or/c (flat (λ (x) (equal? x ,v1))) ,(desugar-one-of v))]))

;; read-con-with : Modules [Listof Symbol] [Listof Symbol] Label S-exp -> Contract
(define (read-con-with modls reqs names mod s)
  (match s
    [`(flat ,e) (flat-c (read-exp-with modls reqs names mod e))]
    [`(,cs ... ,c .. ↦ (λ (,xs ...) ,d))
     (cond
       [(not (= (length xs) (+ 1 (length cs)))) (error "arity mismatch" cs xs)]
       [(not (andmap symbol? xs))
        (error "function* contract: expect symbols, given: " xs)]
       [else
        (func-c (map (curry read-con-with modls reqs names mod) `(,@ cs ,c))
                (read-con-with modls reqs (extend-names xs names) mod d)
                #t)])]
    [`(,cs ... ,c .. ↦ ,d)
     (let ([xs (variables-not-in d (map (const 'z) `(,@ cs ,c)))])
       (read-con-with modls reqs names mod `(,@ cs ,c .. ↦ (λ ,xs ,d))))]
    [`(,cs ... ↦ (λ (,xs ...) ,d))
     (cond
       [(not (= (length xs) (length cs))) (error "arity mismatch" cs xs)]
       [(not (andmap symbol? xs))
        (error "function contract: expect symbols, given: " xs)]
       [else
        (func-c (map (curry read-con-with modls reqs names mod) cs)
                (read-con-with modls reqs (extend-names xs names) mod d)
                #f)])]
    [`(,cs ... ↦ ,d)
     (let ([xs (variables-not-in d (map (const 'z) cs))]) ; desugar independent contract
       (read-con-with modls reqs names mod `(,@ cs ↦ (λ ,xs ,d))))]
    [`(cons/c ,c ,d)
     (cons-c (read-con-with modls reqs names mod c) (read-con-with modls reqs names mod d))]
    [`(or/c ,c ,d) (or-c (read-con-with modls reqs names mod c) (read-con-with modls reqs names mod d))]
    [`(and/c ,c ,d) (and-c (read-con-with modls reqs names mod c) (read-con-with modls reqs names mod d))]
    [`(one-of/c ,v1 ,v ...) (read-con-with modls reqs names mod (desugar-one-of `(,v1 ,@ v)))]
    [`(μ (,x) ,c) (rec-c (read-con-with modls reqs (cons x names) mod c))]
    [x (if (symbol? x)
           (let ([d (name-distance x names)])
             (if (<= 0 d)
                 (ref-c d)
                 (error "unbound: " x)))
           (error "invalid contract form: " x))]))

;; read-exp-with : Modules [Listof Symbol] [Listof Symbol] Label S-exp -> Exp
(define (read-exp-with modls reqs names mod s)
  
  ;; read-and : [Listof S-exp] -> Exp
  (define (read-and terms)
    (match terms
      [`(,t1 ,t2 ,ts ...) (if/ (read-exp-with modls reqs names mod t1)
                               (read-and (rest terms))
                               FALSE)]
      [`(,t) (read-exp-with modls reqs names mod t)]
      [`() TRUE]))
  
  ;; read-or : [Listof S-exp] -> Exp
  (define (read-or terms)
    (match terms
      [`(,t1 ,t2 ,ts ...) (if/ (read-exp-with modls reqs names mod t1)
                               TRUE
                               (read-or (rest terms)))]
      [`(,t) (read-exp-with modls reqs names mod t)]
      [`() FALSE]))
  
  ;; desugar-begin : [Listof S-exp] -> S-Exp
  (define desugar-begin
    (match-lambda
      [`(,e) e]
      [`(,e1 ,e ...) `((λ (_) ,(desugar-begin e)) ,e1)]))
  
  (match s
    [`• BULLET]
    [`(λ (,xs ... ,z ..) ,s)
     (if (and (symbol? z) ((listof symbol?) xs))
         (val (lam (+ 1 (length xs))
                   (read-exp-with
                    modls reqs 
                    (extend-names `(,z) (extend-names xs names)) mod s) #t) ∅)
         (error "λ: expect symbols, given: " xs z))]
    [`(λ (,xs ...) ,s)
     (if ((listof symbol?) xs)
         (val (lam (length xs) (read-exp-with modls reqs (extend-names xs names) mod s) #f) ∅)
         (error "λ: expect symbols, given: " xs))]
    [`(μ (,f) ,s) (if (symbol? f)
                      (rec (read-exp-with modls reqs (cons f names) mod s))
                      (error "μ: expect symbol, given: " f))]
    [`(if ,s1 ,s2 ,s3) (if/ (read-exp-with modls reqs names mod s1)
                            (read-exp-with modls reqs names mod s2)
                            (read-exp-with modls reqs names mod s3))]
    ; currently ignore variable/module named 'else'
    [`(cond [else ,e] ,e1 ...) (read-exp-with modls reqs names mod e)]
    [`(cond [,e1 ,e2] ,e3 ...) (if/ (read-exp-with modls reqs names mod e1)
                                    (read-exp-with modls reqs names mod e2)
                                    (read-exp-with modls reqs names mod (cons 'cond e3)))]
    [`(cond) (blame/ mod mod)]
    [`(and ,terms ...) (read-and terms)]
    [`(or ,terms ...) (read-or terms)]
    [`(let ([,x ,e] ...) ,b) (read-exp-with modls reqs names mod `((λ ,x ,b) ,@e))]
    [`(let* ([,x1 ,e1] ,p ...) ,b)
     (read-exp-with modls reqs names mod `(let ([,x1 ,e1]) (let* ,p ,b)))]
    [`(let* () ,b) (read-exp-with modls reqs names mod `(let () ,b))]
    [`(begin ,e1 ,e ...) (read-exp-with modls reqs names mod (desugar-begin `(,e1 ,@ e)))]
    [`(,f ,xs ...) (app (read-exp-with modls reqs names mod f)
                        (map (curry read-exp-with modls reqs names mod) xs) mod)]
    [x (cond
         [(boolean? x) (if x TRUE FALSE)]
         [(symbol? x)
          (let ([d (name-distance x names)])
            (cond
              [(<= 0 d) (ref d)]
              [else
               (let ([mod-name
                      (ormap (λ (r)
                               (let ([m (mod-by-name modls r)])
                                 (if (modl-exports? m x) r #f)))
                             reqs)])
                 (if mod-name
                     (mod-ref mod-name x mod)
                     (cond
                       [(prim? x) (val x ∅)]
                       [(not (pre-val? x)) (mod-ref mod x mod)]
                       [else (val x ∅)])))]))]
         [(pre-val? x) (val x ∅)]
         [else (error "invalid expression form: " x)])]))

;; extend-names : [Listof Label] [Listof Label] -> [Listof Label]
(define (extend-names new-names old-names)
  (foldl cons old-names new-names))

#|;; show-prog : Prog -> S-exp
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
       [(lam n b v?) 
        (let ([xs (new-var-names n names)])
          `(λ ,(append xs (if v? '(..) '())) ,(show-exp-with (extend-names xs names) b)))]
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
    [(func-c cs d v?)
     (append (map (curry show-con-with names) cs)
             (if v? '(..) '())
             `(↦
               ,(let ([xs (new-var-names (length cs) names)])
                  `(λ ,xs ,(show-con-with (extend-names xs names) d)))))]
    [(cons-c c d) `(cons/c ,(show-con-with names c) ,(show-con-with names d))]
    [(or-c c d) `(or/c ,(show-con-with names c) ,(show-con-with names d))]
    [(and-c c d) `(and/c ,(show-con-with names c) ,(show-con-with names d))]
    [(rec-c c) (let ([x (new-var-name names)])
                 `(μ (,x) ,(show-con-with (cons x names) c)))]
    [(ref-c d) (list-ref names d)]))
|#
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
  (let loop ([pos 0] [xs xs])
    (match xs
      [(cons z zs) (if (equal? z x) pos (loop (+ 1 pos) zs))]
      ['() -1])))

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
       [(lam n b v?) (val (lam n (shift-at ∆ (+ n depth) b) v?) cs)]
       [_ e])]
    [(blame/ l1 l2) e]
    [(app f xs l) (app (shift-at ∆ depth f) (map (curry shift-at ∆ depth) xs) l)]
    [(rec b) (rec (shift-at ∆ (+ 1 depth) b))]
    [(if/ e1 e2 e3)
     (if/ (shift-at ∆ depth e1) (shift-at ∆ depth e2) (shift-at ∆ depth e3))]
    [(mon h f g c e) (mon h f g (shift-con-at ∆ depth c) (shift-at ∆ depth e))]
    [(mod-ref f l m) e]))

;; shift-con : Natural Contract -> Contract
(define (shift-con ∆ c)
  (shift-con-at ∆ 0 c))

;; shift-con-at : Natural Natural Contract -> Contract
(define (shift-con-at ∆ depth c)
  (match c
    [(flat-c e) (flat-c (shift-at ∆ depth e))]
    [(func-c cs1 c2 v?)
     (func-c (map (curry shift-con-at ∆ depth) cs1)
             (shift-con-at ∆ (+ (length cs1) depth) c2)
             v?)]
    [(cons-c c1 c2) (cons-c (shift-con-at ∆ depth c1) (shift-con-at ∆ depth c2))]
    [(or-c c1 c2) (or-c (shift-con-at ∆ depth c1) (shift-con-at ∆ depth c2))]
    [(and-c c1 c2) (and-c (shift-con-at ∆ depth c1) (shift-con-at ∆ depth c2))]
    [(rec-c c1) (rec-c (shift-con-at ∆ (+ 1 depth) c1))]
    [(ref-c x) (if (>= x depth) (ref-c (+ x ∆)) c)]))


;; proc-with-arity? : ValClosure Natural -> [Setof Boolean]
;; checks whether closure represents a procedure compatible with given number of args
(define (proc-with-arity? cl n)
  (match cl
    [(exp-cl (val u cs) ρ)
     (match u
       [(lam m e v?) {set (if v? (<= (- m 1) n) (= m n))}]
       [(constr tag m) {set (= m n)}]
       [(acc tag i) {set (= n 1)}]
       [(constr-check tag) {set (= n 1)}]
       ['• (letrec ([xcludes (exclude 'proc?)]
                    [check-with
                     (match-lambda
                       [(flat-c (val q _)) (if (set-member? xcludes q) 'Refuted 'Neither)]
                       [(flat-c _) 'Neither]
                       [(func-c cs1 d v?)
                        (let ([m (length cs1)])
                          (if (or (and v? (<= (- m 1) n)) (= m n)) 'Proved 'Refuted))]
                       [(cons-c c1 c2) 'Refuted]
                       [(or-c c1 c2) (check-with c2)] ; first-order contract doesn't give new info if it passes
                       [(and-c c1 c2) (if (equal? 'Proved (check-with c1)) 'Proved
                                          (check-with c2))]
                       [(rec-c c) (check-with c)]
                       [(ref-c x) 'Neither])]
                    [r (for/fold ([acc 'Neither]) ([c cs])
                         (match acc
                           ['Neither (check-with (contract-cl-con c))]
                           [_ acc]))])
             (match r
               ['Proved {set #t}]
               ['Refuted {set #f}]
               [_ {set #t #f}]))]
       [_ {set (if (prim? u)
                   (= (op-arity (hash-ref ops u)) n)
                   #f)}])]
    [(mon-fn-cl h f g (contract-cl (func-c cs1 c2 v?) ρc) cl1)
     (let ([m (length cs1)])
       {set (or (and v? (<= (- m 1) n)) (= m n))})]
    [_ {set #f}]))

;; refine : (SetOf ContractClosure) ContractClosure -> (Setof (Setof ContractClosure))
(define (refine cs c)
  (match c
    [(contract-cl (or-c c1 c2) ρc) ; split disjunction
     (set-union (refine cs (close-contract c1 ρc))
                (refine cs (close-contract c2 ρc)))]
    [(contract-cl (and-c c1 c2) ρc)
     (let ([c1′ (close-contract c1 ρc)]
           [c2′ (close-contract c2 ρc)])
       (non-det (λ (cs′)
                  (refine cs′ c2′))
                (refine cs c1′)))]
    [(contract-cl (rec-c c1) ρc) ; unroll recursive contract
     (refine cs (close-contract c1 (env-extend c ρc)))]
    [(contract-cl (flat-c (val (lam 1 (val #t ∅) #f) ∅)) ρ0) {set cs}] ; ignore 'any'
    [(or ; refine with exact value
      (contract-cl (flat-c (val (lam 1 (app (val 'equal? ∅) (list (ref 0) v) _) #f) cs)) ρc)
      (contract-cl (flat-c (val (lam 1 (app (val 'equal? ∅) (list v (ref 0)) _) #f) cs)) ρc))
     {set {set c}}]
    [(contract-cl (flat-c (val p _)) ρc)
     (if (prim? p)
         (match (contracts-imply? cs p)
           ['Refuted ∅]
           ['Proved {set cs}]
           ['Neither {set (set-add cs c)}])
         {set (set-add cs c)})]
    [(contract-cl (cons-c c1 c2) ρc)
     (match (contracts-imply? cs 'cons?)
       ['Refuted ∅]
       [(or 'Proved 'Neither) {set (set-add cs c)}])]
    [(contract-cl (func-c c1s c2 _) ρc)
     (match (contracts-imply? cs 'proc?)
       ['Refuted ∅]
       [(or 'Proved 'Neither) {set (set-add cs c)}])]
    [(contract-cl (ref-c x) ρc) (refine cs (env-get x ρc))]
    [_ {set (set-add cs c)}]))


;; mechanism for proving primitive predicates

(define rules
  ;; (...p?... ⇒ ...q?...) means ((or ... (p? x) ...) implies (and ... (q? x) ...))
  ;; each predicate only appears on the left hand side of one rule
  ;; assume partial order, so there should be no cycle
  `([prime? ⇒ nat?]
    [zero? ⇒ even? nat? non-neg? non-pos?]
    [even? ⇒ int?]
    [odd? ⇒ non-zero? int?]
    [nat? ⇒ int? non-neg?]
    [neg? ⇒ non-pos? non-zero?]
    [pos? ⇒ non-neg? non-zero?]
    [int? non-pos? non-neg? ⇒ real?]
    [non-zero? ⇒ num?]
    [real? ⇒ num?]
    [num? string? proc? cons? nil? ⇒ true?]
    [false? not ⇒ bool?]
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