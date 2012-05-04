#lang racket
(require redex)
(require "cpcf.rkt")

;;;;; Symbolic CPCF
;; add notion of 'pre-value'
;; value is defined as pre-value refined by a set of contracts
(define-extended-language SCPCF CPCF
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

;; converts CPCF terms to SCPCF terms.
;; All plain, concrete values are annotated with an empty set of contracts
;; TODO: would be nicer if language accepts plain values in its syntax...
(define-metafunction SCPCF
  promote : any #|old M|# -> any
  [(promote (λ (X T) any)) ((λ (X T) (promote any)) {})]
  [(promote U) (U {})] ; relies on all old V's being new U's
  [(promote A) A]
  [(promote (mon h f g C M))
   (mon h f g (promote-con C) (promote M))]
  [(promote (any ...)) ((promote any) ...)]
  [(promote any) any]) ; matches X, and non-M, e.g. if, o, type
;; converts CPCF contracts to SCPCF contracts
(define-metafunction SCPCF
  promote-con : any #|old C|# -> C
  [(promote-con (flat any)) (flat (promote any))]
  [(promote-con (C ↦ D)) ((promote-con C) ↦ (promote-con D))]
  [(promote-con (C ↦ (λ (X T) D)))
   ((promote-con C) ↦ (λ (X T) (promote-con D)))])


;;;;; Reduction semantics for Symbolic CPCF
(define SCPCF-red
  (reduction-relation
   SCPCF
   
   ; conditional
   (==> (if ((• T) Cs) M N)
        (if (true? ((• T) Cs)) M N)
        if-apprx)
   (==> (if (tt Cs) M N) M
        if)
   (==> (if (ff Cs) M N) N
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
        β-apprx-blame)
   (==> (μ (X T) M) (subst/s M X (μ (X T) M))
        μ)
   
   ; primitive ops on concrete values
   (==> (o (U Cs) ...) (promote (δ o U ...))
        δ
        ; treat sqrt separately b/c it has some more guarantee in its output
        (side-condition (and (not (term (any-approx? (U Cs) ...)))
                             (not (equal? (term o) (term sqrt))))))
   ; ops that return booleans, non-deterministically
   (==> (o V ...) (promote tt)
        δ-pred-apprx-tt
        (side-condition
         (and (member (term o)
                      (term (zero? non-neg? even? odd? prime? true? false? ∨ ∧)))
              (term (any-approx? V ...)))))
   (==> (o V ...) (promote ff)
        δ-pred-apprx-ff
        (side-condition
         (and (member (term o)
                      (term (zero? non-neg? even? odd? prime? true? false? ∨ ∧)))
              (term (any-approx? V ...)))))
   ; ops that return ints, non-deterministically, no further guarantee in output
   (==> (o V ...) (promote (• Int))
        δ-int-op-apprx
        (side-condition
         (and (member (term o) (term (+ -)))
              (term (any-approx? V ...)))))
   ; sqrt treated separately, with non-neg guarantee in its output
   (==> (sqrt (n Cs)) ((δ sqrt n) {,non-neg/c})
        sqrt)
   (==> (sqrt ((• T) Cs)) ((• Int) {,non-neg/c})
        sqrt-apprx)
   
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
        (promote (λ (X T) (mon h f g D (V (mon h g f C X)))))
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
   ,(if (term (con-∈ C Cs)) (term Proved) (term Neither))])

;; refines given value with more contract(s)
(define-metafunction SCPCF
  refine : V C ... -> V
  [(refine (U (C_0 ...)) C ...) (U (con-∪ (C_0 ...) (C ...)))])

;; checks whether contract is already included in given list/set
(define-metafunction SCPCF
  con-∈ : C Cs -> #t or #f
  [(con-∈ C Cs) ,(ormap (λ (D) (term (con~? C ,D))) (term Cs))])

;; returns union of contract sets. Contracts are identified up to con~?
(define-metafunction SCPCF
  con-∪ : Cs Cs -> Cs
  [(con-∪ Cs Ds) ,(append (filter (λ (C) (not (term (con-∈ ,C Cs))))
                                  (term Ds))
                          (term Cs))])

;; checks whether two contracts are equivalent
;; may give false negatives
;; currently implemented by checking for α-equivalence
(define-metafunction SCPCF
  con~? : C C -> any #|bool|#
  [(con~? C D) ,(equal? (term (normalize-con () C))
                        (term (normalize-con () D)))])

;; turns any close-variable's use into lexical distance to where it was declared
(define-metafunction SCPCF
  normalize : [X ...] M -> any
  [(normalize [Z ...] ((λ (X T) M) {C ...}))
   ((λ (0 0) ; kill irrelevant names
      (normalize [X Z ...] M))
    {(normalize-con [Z ...] C) ...})]
  [(normalize any (U {C ...})) (U {(normalize-con any C) ...})]
  [(normalize any (blame f g)) (blame f g)] ; TODO: kill f and g also??
  [(normalize [Z ...] X) (maybe-index X [Z ...])]
  [(normalize any (M N)) ((normalize any M) (normalize any N))]
  [(normalize [Z ...] (μ (X T) M))
   (μ (0 0) ; kill irrelevant names
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
    ↦ (λ (0 0) ; kill irrelevant names
        (normalize-con [X Z ...] D)))])

;; returns X's position in list, or itself if not found
(define-metafunction SCPCF
  maybe-index : X [X ...] -> n or X
  [(maybe-index X []) X]
  [(maybe-index X [X Z ...]) 0]
  [(maybe-index X [Y Z ...]) ,(+ 1 (term (maybe-index X [Z ...])))])

;; checks if any value is an approximation
(define-metafunction SCPCF
  any-approx? : V ... -> #t or #f
  [(any-approx?) #f]
  [(any-approx? ((• T) Cs) V ...) #t]
  [(any-approx? V_0 V ...) (any-approx? V ...)])

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
  [(havoc (T_x → T_y)) (promote (λ (x (T_x → T_y))
                                  ((havoc T_y) (x (• T_x)))))])


;;;;; type checking for Symbolic CPCF

;; returns expression type, or TypeError
(define-metafunction SCPCF
  type/s : M -> MaybeT
  [(type/s M) (type-check/s () M)])

;; works out expression's type from given type environment
(define-metafunction/extension type-check SCPCF
  type-check/s : TEnv M -> MaybeT
  [(type-check/s TEnv ((• T) {C ...}))
   (maybe-type-val T {(type-check-con/s TEnv C) ...})]
  [(type-check/s TEnv (n {C ...}))
   (maybe-type-val Int {(type-check-con/s TEnv C) ...})]
  [(type-check/s TEnv (b {C ...}))
   (maybe-type-val Bool {(type-check-con/s TEnv C) ...})]
  [(type-check/s ((X_0 T_0) ...) ((λ (X T) M) {C ...}))
   (maybe-type-val 
    (maybe→ T (type-check/s ((X T) (X_0 T_0) ...) M))
    {(type-check-con/s ((X_0 T_0) ...) C) ...})]
  [(type-check/s TEnv (mon h f g C M))
   (maybe-type-mon (type-check-con/s TEnv C) (type-check/s TEnv M))])
;; works out contract's type from given type environment
(define-metafunction/extension type-check-con SCPCF
  type-check-con/s : TEnv C -> MaybeT
  [(type-check-con/s TEnv (flat M)) (maybe-flat (type-check/s TEnv M))])

;; makes sure all contract types agree with value type
(define-metafunction SCPCF
  maybe-type-val : MaybeT (MaybeT ...) -> MaybeT
  [(maybe-type-val T {}) T]
  [(maybe-type-val T {(con T) (con T_s) ...})
   (maybe-type-val T {(cont T_s) ...})]
  [(maybe-type-val any_1 any_2) TypeError])

;; example SCPCF terms
(define s-even? (term (promote ,t-even?)))
(define s-db1 (term (promote ,db1)))
(define s-ap0 (term (promote ,ap0)))
(define s-ap1 (term (promote ,ap1)))
(define s-ap00 (term (promote ,ap00)))
(define s-ap01 (term (promote ,ap01)))
(define s-ap10 (term (promote ,ap10)))
(define s-tri (term (promote ,tri)))
(define prime? (term (promote (λ (x Int) (prime? x)))))
(define prime/c (term (flat ,prime?)))
(define const-true? (term (promote (λ (x Int) tt))))
(define any/c (term (flat ,const-true?))) ; any Int, actually
(define keygen ; opaque
  (term (promote (mon h f g (,any/c ↦ ,prime/c) (• (Int → Int))))))
(define rsa ; opaque
  (term (promote (mon h f g (,prime/c ↦ (,any/c ↦ ,any/c))
                      (• (Int → (Int → Int)))))))
(define rsa-ap
  (term ((,rsa (,keygen (promote 13))) (promote (• Int)))))
(define non-neg/c
  (term (flat (promote (λ (x Int) (non-neg? x))))))
(define sqroot
  (term (promote
         (mon h f g (,non-neg/c ↦ ,non-neg/c)
              (λ (x Int) (sqrt x))))))
(define sqrt-user
  (term (promote (mon h f g ((,any/c ↦ ,any/c) ↦ ,any/c)
                      (λ (f (Int → Int)) (,sqroot (f 0)))))))
(define sqrt-ap-opaque
  (term (promote (,sqrt-user (• (Int → Int))))))
(define sqrt-ap-better
  (term (,sqrt-user ((• (Int → Int)) {(,any/c ↦ ,non-neg/c)}))))

;; test type-checking SCPCF terms
(test-equal (term (type/s ,s-even?)) (term (type ,t-even?)))
(test-equal (term (type/s ,s-db1)) (term (type ,db1)))
(test-equal (term (type/s ,s-ap0)) (term (type ,ap0)))
(test-equal (term (type/s ,s-ap00)) (term (type ,ap00)))
(test-equal (term (type/s ,s-tri)) (term (type ,tri)))
(test-equal (term (type/s ,keygen)) (term (Int → Int)))
(test-equal (term (type/s ,rsa)) (term (Int → (Int → Int))))
(test-equal (term (type/s ,rsa-ap)) (term Int))
(test-equal (term (type/s ,sqroot)) (term (Int → Int)))
(test-equal (term (type/s ,sqrt-user)) (term ((Int → Int) → Int)))
(test-equal (term (type/s ,sqrt-ap-opaque)) (term Int))
(test-equal (term (type/s ,sqrt-ap-better)) (term Int))

;; identify values by ignoring refining contracts
(define (v~? v1 v2)
  (equal? (first v1) (first v2)))

;; test SCPCF term evaluations
(test-->> SCPCF-red #:equiv v~?
          s-ap00 (term (promote 2)))
(test-->> SCPCF-red s-ap01 (term (blame g h)))
(test-->> SCPCF-red #:equiv v~?
          (term (,s-tri (promote 3))) (term (promote 6)))

#;(traces SCPCF-red rsa-ap)
#;(traces SCPCF-red sqrt-ap-opaque)
#;(traces SCPCF-red sqrt-ap-better)

(test-results)