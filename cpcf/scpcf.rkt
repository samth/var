#lang racket
(require redex)
(require "cpcf.rkt")

;;;; Symbolic CPCF
(define-extended-language SCPCF-src CPCF
  ;; closed expression
  [M-closed (side-condition (name m M) (term (closed? m)))]
  ;; allow symbolic value
  [V ....
     (• T)]
  ;; evaluation answer
  [EvalAnswer n
              b
              •
              function
              (blame f g)])

;;;;; Symbolic CPCF, internal representation
;; value now has a set of refining contracts
(define-extended-language SCPCF SCPCF-src
  ; pre-values
  [U (• T)
     (λ (X T) M)
     n
     b]
  ; values
  [V (U Cs)]
  [(Cs Ds) {C ...}]
  ; possible verification results
  [Verified? Proved
             Refuted
             Neither])

;; converts SCPCF-src terms to their internal representations by
;; (recursively) annotating values with an empty set of refining contracts
;; TODO: would be nicer if language accepts plain values in its syntax...
(define-metafunction SCPCF
  convert : any #|SCPCF-src term|# -> M
  [(convert M) M] ; just to make it more flexible
  [(convert (λ (X T) any)) ((λ (X T) (convert any)) {})]
  [(convert U) (U {})] ; relies on all old V's being new U's
  [(convert (μ (X T) any)) (μ (X T) (convert any))]
  [(convert (if any ...)) (if (convert any) ...)]
  [(convert (o any ...)) (o (convert any) ...)]
  [(convert (mon h f g any_C any_M))
   (mon h f g (convert-con any_C) (convert any_M))]
  [(convert (any_M1 any_M2)) ((convert any_M1) (convert any_M2))]
  ;; matches A and X:
  [(convert any_M) any_M])
;; converts CPCF contracts to SCPCF contracts
(define-metafunction SCPCF
  convert-con : any #|SCPCF-src contract|# -> C
  [(convert-con (flat any)) (flat (convert any))]
  [(convert-con (any_C ↦ any_D)) ((convert-con any_C) ↦ (convert-con any_D))]
  [(convert-con (any_C ↦ (λ (X T) any_D)))
   ((convert-con any_C) ↦ (λ (X T) (convert-con any_D)))])


;;;;; Reduction semantics for Symbolic CPCF
(define SCPCF-red
  (reduction-relation
   SCPCF
   
   ; conditional
   (==> (if V M N) M
        (side-condition (member (term (convert #t)) (term (δ/s true? V))))
        if)
   (==> (if V M N) N
        (side-condition (member (term (convert #f)) (term (δ/s true? V))))
        if-not)
   
   ; function application
   (==> (((λ (X T) M) Cs) V) (subst/s M X V)
        ; TODO: examine what's going on. So we lose Cs?
        β)
   (==> (((• (T_x → T_y)) Cs) V)
        ((• T_y) ,(map (λ (c) (term (subst-range-con ,c V))) (term Cs)))
        β-apprx-ok)
   (==> (((• (T_x → T_y)) Cs) V)
        ((havoc T_x) V)
        β-apprx-havoc)
   (==> (μ (X T) M) (subst/s M X (μ (X T) M))
        μ)
   
   ; primitive ops (non-deterministic)
   (==> (o V ...) V_i
        δ
        (where {V_1 ... V_i V_n ...} (δ/s o V ...)))
   
   ; contract checking
   (==> (mon h f g C V) V
        mon-verified
        (side-condition (equal? (term Proved) (term (verify V C)))))
   (==> (mon h f g (flat M) V)
        ; TODO: confirm: paper says (blame f g), i think they mean (blame f h)
        (if (M V) (refine V (flat M)) (blame f h))
        mon-flat
        (side-condition (equal? (term Neither) (term (verify V (flat M))))))
   (==> (mon h f g (C ↦ (λ (X T) D)) V)
        (convert (λ (X T) (mon h f g D (V (mon h g f C X)))))
        mon-fun)
   (==> (mon h f g (C ↦ D) V)
        (mon h f g (C ↦ (λ (X ⊥) D)) V)
        (where X ,(variable-not-in (term (D V)) (term dummy)))
        mon-desugar)
   
   (--> (in-hole E (blame f g)) (blame f g)
        blame-prop
        (side-condition (not (equal? (term E) (term hole)))))
   with
   [(--> (in-hole E M) (in-hole E N)) (==> M N)]))

;; interprets primitive ops
(define-metafunction SCPCF
  ; i restrict the range just to prevent myself from making this
  ; out of sync with above rules
  δ/s : o V ... -> {V ...}
  ; sqrt treated separately due to refinement in result
  [(δ/s sqrt (n Cs)) {((δ sqrt n) {(convert-con ,non-neg/c)})}]
  [(δ/s sqrt ((• T) Cs)) {((• Int) {(convert-con ,non-neg/c)})}]
  ; exact answer for concrete arguments
  [(δ/s o (U Cs) ...)
   {((δ o U ...) {})}
   (side-condition (term (all-concrete? U ...)))]
  ; full range answer for functions returning boolean
  [(δ/s o V ...)
   {(convert #t) (convert #f)}
   (side-condition
    (member (term o)
            (term (zero? non-neg? even? odd? prime? true? false? ∨ ∧))))]
  ; full range answer for functions returning ints
  [(δ/s o V ...)
   {(convert (• Int))}
   (side-condition (member (term o) (term (+ -))))])


;; substitute V into X in function contract's range
(define-metafunction SCPCF
  subst-range-con : C V -> C
  ; partial function on C, will error out on flat contracts
  [(subst-range-con (C ↦ (λ (X T) D)) V) (subst-con/s D X V)]
  [(subst-range-con (C ↦ D) V) D])

;; checks whether value proves contract
(define-metafunction SCPCF
  verify : V C -> Verified?
  [(verify (U Cs) C)
   ,(if (ormap (λ (c) (term (con~? ,c C))) (term Cs))
        (term Proved)
        (term Neither))])

;; refines given value with more contract(s)
;; assume value does not currently prove contract(s)
(define-metafunction SCPCF
  refine : V C ... -> V
  [(refine (U {C ...}) D ...) (U {D ... C ...})])

;; checks whether two contracts are equivalent
;; may give false negatives
;; currently implemented by checking for α-equivalence
(define-metafunction SCPCF
  con~? : C C -> #t or #f
  [(con~? C D) ,(equal? (term (normalize-con () C))
                        (term (normalize-con () D)))])

;; checks whether expression is closed
(define-metafunction SCPCF-src
  closed? : M -> #t or #f
  [(closed? M) (closed-by? [] M)])
(define-metafunction SCPCF-src
  closed-by? : [X ...] M -> #t or #f
  [(closed-by? [X ...] (λ (Z T) M)) (closed-by? [Z X ...] M)]
  [(closed-by? any A) #t]
  [(closed-by? [X_1 ... X X_n ...] X) #t]
  [(closed-by? any X) #f]
  [(closed-by? any (M_1 M_2)) ,(and (term (closed-by? any M_1))
                                    (term (closed-by? any M_2)))]
  [(closed-by? [X ...] (μ (Z T) M)) (closed-by? [Z X ...] M)]
  [(closed-by? any (if M_1 M_2 M_3)) ,(and (term (closed-by? any M_1))
                                           (term (closed-by? any M_2))
                                           (term (closed-by? any M_3)))]
  [(closed-by? any (o M ...)) ,(andmap (compose not false?)
                                       (term ((closed-by? any M) ...)))]
  [(closed-by? any (mon h f g C M))
   ,(and (term (con-closed-by? any C)) (term (closed-by? any M)))])
(define-metafunction SCPCF-src
  con-closed-by? : [X ...] C -> #t or #f
  [(con-closed-by? any (flat M)) (closed-by? any M)]
  [(con-closed-by? any (C ↦ D)) ,(and (term (con-closed-by? any C))
                                      (term (con-closed-by? any D)))]
  [(con-closed-by? [X ...] (C ↦ (λ (Z T) D)))
   ,(and (term (con-closed-by? [X ...] C))
         (term (con-closed-by? [Z X ...] D)))])

;; turns any close-variable's use into lexical distance to where it was declared
(define-metafunction SCPCF
  normalize : [X ...] M -> any
  [(normalize [Z ...] ((λ (X T) M) {C ...}))
   ((λ _ ; kill irrelevant names
      (normalize [X Z ...] M))
    {(normalize-con [Z ...] C) ...})]
  [(normalize any (U {C ...})) (U {(normalize-con any C) ...})]
  [(normalize any (blame f g)) (blame f g)] ; TODO: kill f and g also??
  [(normalize [Z ...] X) (maybe-index 0 X [Z ...])]
  [(normalize any (M N)) ((normalize any M) (normalize any N))]
  [(normalize [Z ...] (μ (X T) M))
   (μ _ ; kill irrelevant names
      (normalize [X Z ...] M))]
  [(normalize any (if M ...)) (if (normalize any M) ...)]
  [(normalize any (o M ...)) (o (normalize any M) ...)]
  [(normalize any (mon h f g C M))
   ; TODO: kill h,f,g also??
   (mon h f g (normalize-con any C) (normalize any M))])
(define-metafunction SCPCF
  normalize-con : [X ...] C -> any
  [(normalize-con any (flat M)) (flat (normalize any M))]
  [(normalize-con any (C ↦ D))
   (normalize-con any (C ↦ (λ (X ⊥) D)))
   (where X ,(variable-not-in (term D) (term dummy)))]
  [(normalize-con [Z ...] (C ↦ (λ (X T) D)))
   ((normalize-con [Z ...] C)
    ↦ (λ _ ; kill irrelevant names
        (normalize-con [X Z ...] D)))])

;; returns X's position in list, or itself if not found
(define-metafunction SCPCF
  maybe-index : n X [X ...] -> n or X
  [(maybe-index n X []) X]
  [(maybe-index n X [X Z ...]) n]
  [(maybe-index n X [Y Z ...]) (maybe-index ,(+ 1 (term n)) X [Z ...])])

;; checks whether all prevalues are concrete
(define-metafunction SCPCF
  all-concrete? : U ... -> #t or #f
  [(all-concrete?) #t]
  [(all-concrete? (• T) U ...) #f]
  [(all-concrete? U_0 U ...) (all-concrete? U ...)])

;; capture-avoiding substitution for SCPCF terms
(define-metafunction/extension subst SCPCF
  subst/s : any X M -> any
  [(subst/s ((λ (X T) M) Cs) X N) ((λ (X T) M) Cs)] ; var bound, ignore
  [(subst/s ((λ (X T) M) Cs) Y N)
   ((λ (Z T)
      (subst/s (subst/s M X Z) Y N)) Cs) ; TODO exponential blow-up risk
   (where Z ,(variable-not-in (term (M Y N)) (term X)))]
  [(subst/s (mon h f g C M) X N)
   (mon h f g (subst-con/s C X N) (subst/s M X N))])
;; capture-avoiding substitution for SCPCF contracts
(define-metafunction/extension subst-con SCPCF
  subst-con/s : C X M -> C
  [(subst-con/s (flat M) X N) (flat (subst/s M X N))])

;; TODO: examine what havoc really does
(define-metafunction SCPCF
  havoc : T -> M
  [(havoc B) (μ (X B) X)]
  [(havoc (T_x → T_y)) (convert (λ (x (T_x → T_y))
                                  ((havoc T_y) (x (• T_x)))))])


;;;;; type checking for Symbolic CPCF

;; returns expression type, or TypeError
(define-metafunction SCPCF-src
  type/s : M -> MaybeT
  [(type/s M) (type-check/s () M)])

;; works out expression's type from given type environment
(define-metafunction/extension type-check SCPCF-src
  type-check/s : TEnv M -> MaybeT
  [(type-check/s TEnv (• T)) T]
  [(type-check/s TEnv (mon h f g C M))
   (maybe-type-mon (type-check-con/s TEnv C) (type-check/s TEnv M))])
;; works out contract's type from given type environment
(define-metafunction/extension type-check-con SCPCF-src
  type-check-con/s : TEnv C -> MaybeT
  [(type-check-con/s TEnv (flat M)) (maybe-flat (type-check/s TEnv M))])

;; eval-red : S-exp -> [Setof EvalAnswer]
;; evaluates well-typed, closed expression from SCPCF-src
(define (eval-red s)
  (list->set (term (eval (convert ,s)))))

;; eval function in terms of reduction relation
(define-metafunction SCPCF
  eval : M -> [EvalAnswer ...]
  [(eval M)
   ,(map (λ (t) (term (get-answer ,t)))
         (filter answer? (apply-reduction-relation* SCPCF-red (term M))))])

;; checks whether given s-exp is an Answer Expression in SCPCF
(define (answer? x)
  (redex-match SCPCF A x))

;; converts answer-expression to eval-answer
(define-metafunction SCPCF
  get-answer : A -> EvalAnswer
  [(get-answer ((• (T_1 → T_2)) Cs)) function]
  [(get-answer ((• T) Cs)) •]
  [(get-answer (blame f g)) (blame f g)]
  [(get-answer ((λ (X T) M) Cs)) function]
  [(get-answer (U Cs)) U])

;; example SCPCF terms
(define prime? (term (λ (x Int) (prime? x))))
(define prime/c (term (flat ,prime?)))
(define const-true? (term (λ (x Int) #t)))
(define any/c (term (flat ,const-true?))) ; any Int, actually
(define keygen ; opaque
  (term (mon h f g (,any/c ↦ ,prime/c) (• (Int → Int)))))
(define rsa ; opaque
  (term (mon h f g (,prime/c ↦ (,any/c ↦ ,any/c))
             (• (Int → (Int → Int))))))
(define rsa-ap
  (term ((,rsa (,keygen 13)) (• Int))))
(define non-neg/c
  (term (flat (λ (x Int) (non-neg? x)))))
(define sqroot
  (term (mon h f g (,non-neg/c ↦ ,non-neg/c)
             (λ (x Int) (sqrt x)))))
(define sqrt-user
  (term (mon h f g ((,any/c ↦ ,any/c) ↦ ,any/c)
             (λ (f (Int → Int)) (,sqroot (f 0))))))
(define sqrt-ap-opaque
  (term (,sqrt-user (• (Int → Int)))))
(define sqrt-ap-better ; SCPCF term, not SCPCF-src
  (term ((convert ,sqrt-user)
         ((• (Int → Int)) {(convert-con (,any/c ↦ ,non-neg/c))}))))
(define tri-ap-abs ; currently does not terminate
  (term (,tri (• Int))))
(define tri-acc ; computes sum[1..n] using accumulator
  (term (μ (f (Int → (Int → Int)))
           (λ (n Int)
             (λ (acc Int)
               (if (zero? n) acc
                   ((f (- n 1)) (+ acc n))))))))
(define tri-acc-ap
  (term ((,tri-acc (• Int)) (• Int))))

;; test type-checking SCPCF terms
(test-equal (term (type/s ,t-even?)) (term (type ,t-even?)))
(test-equal (term (type/s ,db1)) (term (type ,db1)))
(test-equal (term (type/s ,ap0)) (term (type ,ap0)))
(test-equal (term (type/s ,ap00)) (term (type ,ap00)))
(test-equal (term (type/s ,tri)) (term (type ,tri)))
(test-equal (term (type/s ,keygen)) (term (Int → Int)))
(test-equal (term (type/s ,rsa)) (term (Int → (Int → Int))))
(test-equal (term (type/s ,rsa-ap)) (term Int))
(test-equal (term (type/s ,sqroot)) (term (Int → Int)))
(test-equal (term (type/s ,sqrt-user)) (term ((Int → Int) → Int)))
(test-equal (term (type/s ,sqrt-ap-opaque)) (term Int))
#;(test-equal (term (type/s ,sqrt-ap-better)) (term Int))
(test-equal (term (type/s ,tri-acc)) (term (Int → (Int → Int))))

;; identify values by ignoring refining contracts
(define (v~? v1 v2)
  (equal? (first v1) (first v2)))

;; test SCPCF term evaluations
(test-equal (eval-red ap00) {set (term 2)})
(test-equal (eval-red ap01) {set (term (blame g h))})
(test-equal (eval-red (term (,tri 3))) {set (term 6)})
(test-equal (eval-red tri-acc-ap) {set (term •)})
(test-equal (eval-red rsa-ap) {set (term •) (term (blame f h))})
(test-equal (eval-red sqrt-ap-opaque) {set (term •) (term (blame g h))})
(test-equal (eval-red sqrt-ap-better) {set (term •)})

#;(traces SCPCF-red (term (convert ,rsa-ap)))
#;(traces SCPCF-red (term (convert ,sqrt-ap-opaque)))
#;(traces SCPCF-red sqrt-ap-better)
#;(traces SCPCF-red (term (convert (,tri (• Int))))) ; unbound # states
#;(traces SCPCF-red (term (convert ,tri-acc-ap))) ; finite # states

(test-results)

;; verify consistency with racket model
(require "in-racket/scpcf-eval.rkt")
(require (only-in "in-racket/scpcf-lang.rkt"
                  read-exp [type-check tc] show-type))

;; mutable refs for accumulating results
(define count 0)
(define cpu1 0)
(define real1 0)
(define gc1 0)
(define cpu2 0)
(define real2 0)
(define gc2 0)

(redex-check
 SCPCF-src
 M-closed
 (let* ([t1 (term (type/s M-closed))]
        [t2 ((compose show-type tc read-exp) (term M-closed))])
   (and (equal? t1 t2)
        (or (equal? t1 'TypeError)
            (let-values
                ([(a1 cpu1′ real1′ gc1′)
                  (time-apply eval-red (list (term M-closed)))]
                 [(a2 cpu2′ real2′ gc2′)
                  (time-apply eval-cek (list (term M-closed)))])
              ;; update statistics
              (set! count (add1 count))
              (set! cpu1 (+ cpu1 cpu1′))
              (set! real1 (+ real1 real1′))
              (set! gc1 (+ gc1 gc1′))
              (set! cpu2 (+ cpu2 cpu2′))
              (set! real2 (+ real2 real2′))
              (set! gc2 (+ gc2 gc2′))
              ;; assert equivalence
              (equal? a1 a2)))))
 #:attempts 5000)

`(,count programs were well-typed)
`(eval-red total: (cpu: ,cpu1) (real: ,real1) (gc: ,gc1))
`(eval-cek total: (cpu: ,cpu2) (real: ,real2) (gc: ,gc2))

;; The time taken to run this test increased significantly when I inserted
;; those set! statements. It didn't finish after 20 minutes. How can ~35k
;; additions make such a big difference, even if the numbers are boxed?
;; I tried changing memory limit from 1024M to 2048M and it finished quickly.
;; Result on Ubuntu 12.04, T8100:
#;'(4121 programs were well-typed)
#;'(eval-red total: (cpu: 1060) (real: 1217) (gc: 124))
#;'(eval-cek total: (cpu: 324) (real: 290) (gc: 20))

;; Results on samth's machine:
;; '(4126 programs were well-typed)
;; '(eval-red total: (cpu: 980) (real: 948) (gc: 28))
;; '(eval-cek total: (cpu: 216) (real: 181) (gc: 8))
