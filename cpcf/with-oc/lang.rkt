#lang racket
(require redex)
(require (except-in "lang-simple.rkt" subst subst-c))

(provide
 scpcf δ desug
 default-o acc-o subst subst-c var-not-in
 Γ-flush del Γ-del Γ-reset Γ-mk Γ-upd dom :: Γ:: ! split-cons D-ranges
 refine-v Γ-refine flat-refine
 s-map rem-dup #;non-det: remove-duplicates
 c/any C/ANY c/int C/INT c/str C/STR c/bool C/BOOL)

(define-extended-language scpcf cpcf
  ; expression
  [e ....
     ; syntactic sugar:
     (and e e ...)
     (or e e ...)
     (let (x e) e)
     (let ([x e] [x e] ...) e)
     (cond [e e] ... [else e])
     (begin e e ...)
     •]
  
  ; primitives
  [o1 .... sub1 str-len car cdr]
  [o2 .... - *]
  [p? .... true? bool? str? int? proc? cons? zero?]
  [v .... (• CC ...)]
  [b .... s]
  [bool #t #f]
  [s string]
  [φ p? (¬ p?)]
  
  ; environments
  [O ([x ↦ o′] ...)]
  [Γ ([o′ ↦ φ ...] ...)]
  
  ; path
  [o ∅ o′]
  [o′ (acc ... x)]
  [acc car cdr]
  
  ; closures
  [C (e ρ O ψ)]
  [V (v ρ O ψ) (Cons V V) (arr D V)]
  [D (flat V)
     (c ↦ (λ (x) c) ρ O ψ)
     (or/c c c ρ O ψ)
     (and/c c c ρ O ψ)
     (cons/c c c ρ O ψ)]
  [CC (c ρ O ψ)]
  
  ; interpreter answer
  [ea n s bool function • (• p? ...) ERR (cons ea ea)]
  
  ; verification answer
  [Verified? Proved Refuted Neither])

(define c/any (term (flat tt)))
(define C/ANY (term (,c/any [] [] [])))
(define c/int (term (flat int?)))
(define C/INT (term (,c/int [] [] [])))
(define c/str (term (flat str?)))
(define C/STR (term (,c/str [] [] [])))
(define c/bool (term (flat bool?)))
(define C/BOOL (term (,c/bool [] [] [])))

;; extract function contract's domain
(define-metafunction scpcf ; FIXME obsolete
  D-ranges : (D ...) -> (D ...)
  [(D-ranges ()) ()]
  [(D-ranges (((c_1 ↦ (λ (x) c_2)) ρ O ψ) any ...))
   ,(cons (term (c_2 (:: ρ [x ↦ ((•) [] [] [])])
                     (:: O [x ↦ x])))
          (term (D-ranges (any ...))))]
  [(D-ranges (any_1 any ...)) (D-ranges (any ...))])

;; 'flushes' all propositions in Γ into ρ as refinining contracts for •'s
(define-metafunction scpcf
  Γ-flush : Γ ρ -> ρ
  [(Γ-flush [] ρ) ρ]
  [(Γ-flush ([x ↦ φ ...] any ...) (any_1 ... [x ↦ ((• CC ...) ρ O ψ)] any_2 ...))
   (Γ-flush (any ...)
          (any_1 ... [x ↦ ((• (mk-D () φ) ... CC ...) [] [] [])] any_2 ...))]
  [(Γ-flush ([(acc ... x) ↦ φ ...] any ...)
          (any_1 ... [x ↦ ((• CC ...) ρ O ψ)] any_2 ...))
   (Γ-flush (any ...)
          (any_1 ... [x ↦ ((• (mk-D (acc ...) φ) ... CC ...) [] [] [])] any_2 ...))]
  [(Γ-flush (any_1 any ...) ρ) (Γ-flush (any ...) ρ)])

;; check whether value satisfies contract
(define-metafunction scpcf
  V⊢? : V CC -> Verified?
  [(V⊢? ((• any_1 ... CC any_2 ...) ρ O ψ) CC_1)
   Proved
   (where #t (CC-implies? CC CC_1))]
  [(V⊢? ((• any_1 ... C any_2 ...) ρ O ψ) CC_1)
   Refuted
   (where #t (D-excludes? CC CC_1))]
  [(V⊢? V CC) Neither])

;; uses existing information to check whether the predicate holds
(define-metafunction scpcf
  ⊢? : (CC ...) Γ o p? -> Verified?
  ; Γ is easier/cheaper, so use it first
  [(⊢? (CC ...) Γ o p?) ,(match (term (Γ⊢? Γ o p?))
                          ['Proved (term Proved)]
                          ['Refuted (term Refuted)]
                          ['Neither (term (C⊢? (CC ...) p?))])])

;; checks whether contract set can prove/refute predicate
(define-metafunction scpcf
  C⊢? : (CC ...) p? -> Verified?
  [(C⊢? (any_1 ... ((flat p?) ρ O ψ) any_2 ...) p?_1)
   Proved
   (where #t (implies? p? p?_1))]
  [(C⊢? (any_1 ... ((flat p?) ρ O ψ) any_2 ...) p?_1)
   Refuted
   (where #t (excludes? p? p?_1))]
  [(C⊢? any p?) Neither])

;; checks whether proposition set can prove/refute predicate
(define-metafunction scpcf
  Γ⊢? : Γ o p? -> Verified?
  [(Γ⊢? (any_1 ... [o′ ↦ any_3 ... p? any_4 ...] any_2 ...) o′ p?_1)
   Proved
   (where #t (implies? p? p?_1))]
  [(Γ⊢? (any_1 ... [o′ ↦ any_3 ... p? any_4 ...] any_2 ...) o′ p?_1)
   Refuted
   (where #t (excludes? p? p?_1))]
  [(Γ⊢? (any_1 ... [o′ ↦ any_3 ... (¬ p?) any_4 ...] any_2 ...) o′ p?_1)
   Refuted
   (where #t (implies? p?_1 p?))]
  [(Γ⊢? any_Γ any_o any_p?) Neither])

;; checks predicates on concrete values
(define-metafunction scpcf
  concrete-check : p? V -> bool
  [(concrete-check int? (n ρ O ψ)) #t]
  [(concrete-check zero? (0 ρ O ψ)) #t]
  [(concrete-check str? (s ρ O ψ)) #t]
  [(concrete-check false? (#f ρ O ψ)) #t]
  [(concrete-check false? V) #f]
  [(concrete-check bool? (bool ρ O ψ)) #t]
  [(concrete-check proc? ((λ (x) e) ρ O ψ)) #t]
  [(concrete-check proc? (arr D V)) #t]
  [(concrete-check proc? (op ρ O ψ)) #t]
  [(concrete-check true? (#f ρ O ψ)) #f]
  [(concrete-check true? V) #t]
  [(concrete-check cons? (Cons V_1 V_2)) #t]
  [(concrete-check p? V) #f])

(define-metafunction scpcf
  desug : e -> e
  [(desug (λ (x) e)) (λ (x) (desug e))]
  [(desug v) v]
  [(desug x) x]
  [(desug (e_0 e_1 e_2 ...)) ((desug e_0) (desug e_1) (desug e_2) ...)]
  [(desug (if e e_1 e_2)) (if (desug e) (desug e_1) (desug e_2))]
  [(desug (mon c e)) (mon (desug-c c) (desug e))]
  [(desug (μ (x) e)) (μ (x) (desug e))]
  [(desug (and e)) (desug e)]
  [(desug (and e_1 e_2 ...)) (if (desug e_1) (desug (and e_2 ...)) #f)]
  [(desug (or e)) (desug e)]
  [(desug (or e_1 e_2 ...))
   ((λ (x_tmp) (if x_tmp x_tmp (desug (or e_2 ...)))) (desug e_1))
   (where x_tmp ,(variable-not-in (term (e_1 e_2 ...)) (term tmp)))]
  [(desug (let [x e_x] e)) ((λ (x) (desug e)) (desug e_x))]
  [(desug (let ([x e_x]) e)) ((λ (x) (desug e)) (desug e_x))]
  [(desug (let ([x_1 e_1] [x_2 e_2] ...) e))
   ((λ (x_1) (desug (let ([x_2 e_2] ...) e))) (desug e_1))]
  [(desug (cond [else e])) (desug e)]
  [(desug (cond [e_1 e_2] any ...))
   (if (desug e_1) (desug e_2) (desug (cond any ...)))]
  [(desug (begin e)) (desug e)]
  [(desug (begin e_1 e_2 ...))
   ((λ (x_tmp) (desug (begin e_2 ...))) (desug e_1))
   (where x_tmp ,(variable-not-in (term (e_1 e_2 ...)) (term tmp)))]
  [(desug •) (•)])

(define-metafunction scpcf
  desug-c : c -> c
  [(desug-c (flat e)) (flat (desug e))]
  [(desug-c (or/c c_1 c_2)) (or/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (and/c c_1 c_2)) (and/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (cons/c c_1 c_2)) (cons/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (c_x ↦ (λ (x) c_y))) ((desug-c c_x) ↦ (λ (x) (desug-c c_y)))]
  [(desug-c (μ (x) c)) (μ (x) (desug-c c))]
  [(desug-c x) x])

(define-metafunction scpcf
  flat-refine : V V -> V
  [(flat-refine ((• CC ...) ρ O ψ) (v ρ_c O_c ψ_c))
   ((• ((flat v) ρ_c O_c ψ_c) CC ...) ρ O ψ)]
  [(flat-refine V V_p) V])

;; refines value with given (closed) contract
(define-metafunction scpcf
  refine-v : V CC -> {V ...}
  [(refine-v ((• CC_1 ...) ρ O ψ) CC)
   ,(s-map
     (λ (Cs) (term ((• ,@ Cs) ρ O ψ)))
     (term (refine (CC_1 ...) CC)))]
  [(refine-v V CC) {V}])

;; refines set of contracts with another contract
(define-metafunction scpcf
  refine : {D ...} D -> {{D ...} ...}
  
  ; special cases where we can do something smarter
  [(refine {any_1 ... D_1 any_2 ...} D_2)
   {{any_1 ... D_1 any_2 ...}}
   (where #t (CC-implies? D_1 D_2))] ; refining contract is redundant
  [(refine {any_1 ... D_1 any_2 ...} D_2)
   {{any_1 ... D_2 any_2 ...}}
   (where #t (CC-implies? D_2 D_1))] ; one of the old contract is redundant
  [(refine {any_1 ... D_1 any_2 ...} D_2)
   {}
   (where #t (D-excludes? D_1 D_2))] ; the refinement is bullshit
  
  ; general cases
  [(refine any ((or/c c_1 c_2) ρ O ψ)) ; split disjunction for better precision
   ,(∪ (term (refine any (c_1 ρ O ψ))) (term (refine any (c_2 ρ O ψ))))]
  [(refine any ((and/c c_1 c_2) ρ O ψ)) ; break conjunction into smaller refinements
   ,(s-map
     (λ (Cs)
       (term (refine ,Cs (c_2 ρ O ψ))))
     (term (refine any (c_2 ρ O ψ))))]
  [(refine any ((μ (x) c) ρ O ψ)) ; unroll recursive contract
   (refine any (c (:: [x ↦ ((μ (x) c) ρ O ψ)] ρ)
                  (:: [x ↦ x] O)))]
  [(refine any (x ρ O ψ)) (refine any (! ρ x))]
  [(refine {D ...} D_1) {{D_1 D ...}}])

;; checks whether first contract (definitely) implies second
;; may give false negative
(define-metafunction scpcf
  CC-implies? : CC CC -> bool
  [(CC-implies? ((flat p?) ρ O ψ) ((flat p?_1) ρ_1 O_1)) (implies? p? p?_1)]
  [(CC-implies? CC_1 CC_2) #f])

;; checks whether first contract (definitely) contradicts second
;; may give false negative
(define-metafunction scpcf
  D-excludes? : D D -> bool
  [(D-excludes? ((flat p?) ρ O ψ) ((flat p?_1) ρ_1 O_1)) (excludes? p? p?_1)]
  [(D-excludes? D_1 D_2) #f])

;; checks whether first proposition (definitely) implies second
(define-metafunction scpcf
  φ-implies? : φ φ -> bool
  [(φ-implies? p? p?_1) (implies? p? p?_1)]
  [(φ-implies? (¬ p?) (¬ p?_1)) (implies? p?_1 p?)]
  [(φ-implies? p? (¬ p?_1)) (excludes? p? p?_1)]
  [(φ-implies? (¬ true?) false?) #t]
  [(φ-implies? (¬ false? true?)) #t]
  [(φ-implies? (¬ p?) p?_1) #f])

;; checks whether first predicate implies second
(define-metafunction scpcf
  implies? : p? p? -> bool
  [(implies? p? tt) #t]
  [(implies? p? p?) #t]
  [(implies? false? true?) #f]
  [(implies? p? true?) #t]
  [(implies? p? p?_1) #f])

;; checks whether first predicate contradicts second
(define-metafunction scpcf
  excludes? : p? p? -> bool
  [(excludes? p? p?_1)
   ,(ormap (λ (S) (and (not (equal? (term p?) (term p?_1)))
                       (member (term p?) S)
                       (member (term p?_1) S) #t #| #t here to force bool |#))
           `((true? false?)
             (int? str? bool? proc? cons?)))])



;; use propositions in Γ to refine value
(define-metafunction scpcf
  Γ-refine : V Γ o′ -> V
  [(Γ-refine ((• CC ...) ρ O ψ) ([(acc ... acc_1 ... x) ↦ φ ...] any ...) (acc_1 ... x))
   (Γ-refine ((• (mk-D (acc ...) φ) ... CC ...) ρ O ψ) (any ...) (acc_1 ... x))]
  [(Γ-refine ((• CC ...) ρ O ψ) (any any_1 ...) o′)
   (Γ-refine ((• CC ...) ρ O ψ) (any_1 ...) o′)]
  [(Γ-refine V Γ o′) V])

;; makes (closed) contract out of proposition
(define-metafunction scpcf
  mk-D : (acc ...) φ -> (c ρ O ψ)
  [(mk-D any p?) ((mk-c any (flat p?)) [] [] [])]
  ; lose precision for now until we have not/c?
  [(mk-D any (¬ p?)) ((flat tt) [] [] [])])
;; constructs contract for given path of accessors
(define-metafunction scpcf
  mk-c : (acc ...) c -> c
  [(mk-c () c) c]
  [(mk-c (car acc ...) c) (mk-c (acc ...) (cons/c c ,c/any))]
  [(mk-c (cdr acc ...) c) (mk-c (acc ...) (cons/c ,c/any c))])

;; removes x from Γ's domain
(define-metafunction scpcf
  Γ-del : Γ x ... -> Γ
  [(Γ-del (any ... [(acc ... x) ↦ φ ...] any_1 ...) x_1 ... x x_2 ...)
   (Γ-del (any ... any_1 ...) x_1 ... x x_2 ...)]
  [(Γ-del Γ x ...) Γ])

;; overrides Γ with [x ↦ tt]
(define-metafunction scpcf
  Γ-reset : Γ x -> Γ
  [(Γ-reset Γ x) ,(cons (term [(x) ↦ tt]) (term (Γ-del Γ x)))])

;; returns environment's domain. (overloaded on closures)
(define-metafunction scpcf
  dom : any -> {x ...}
  [(dom ([(acc ... x) ↦ any ...] ...)) (remove-duplicates (x ...))]
  [(dom ([x ↦ any ...] ...)) (x ...)])

(define-metafunction scpcf
  remove-duplicates : {any ...} -> {any ...}
  [(remove-duplicates (any_1 ... any any_2 ... any any_3 ...))
   (remove-duplicates (any_1 ... any_2 ... any any_3 ...))]
  [(remove-duplicates any) any])

;; makes proposition environment with given domain and updates it with Γ
(define-metafunction scpcf
  Γ-mk : {x ...} Γ -> Γ
  [(Γ-mk {x ...} Γ) (Γ-upd ([(x) ↦ tt] ...) Γ)])

;; updates Γ1 with propositions from Γ2 if they talk about the same variable
(define-metafunction scpcf
  Γ-upd : Γ Γ -> Γ
  [(Γ-upd any []) any]
  [(Γ-upd (any_1 ... [o′ ↦ φ ...] any_2 ...) ([o′ ↦ φ_1 ...] any_3 ...))
   (Γ-upd (any_1 ... [o′ ↦ φ_1 ...] any_2 ...) (any_3 ...))]
  [(Γ-upd (any_1 ... [(acc_1 ... x) ↦ φ ...] any_2 ...)
          ([(acc ... x) ↦ φ_1 ...] any_3 ...))
   (Γ-upd ([(acc ... x) ↦ φ_1 ...] any_1 ... [(acc_1 ... x) ↦ φ ...] any_2 ...)
          (any_3 ...))]
  [(Γ-upd any (any_1 any_2 ...)) (Γ-upd any (any_2 ...))])

;; updates proposition environment with proposition
(define-metafunction scpcf
  Γ:: : Γ φ o -> Γ
  [(Γ:: any_Γ any_φ ∅) any_Γ]
  [(Γ:: (any ... [o ↦ tt] any_1 ...) φ o) (any ... [o ↦ φ] any_1 ...)]
  [(Γ:: (any ... [o ↦ φ_1 ... φ φ_n ...] any_1 ...) φ o)
   (any ... [o ↦ φ_1 ... φ φ_n ...] any_1 ...)]
  [(Γ:: (any_1 ... [o ↦ any ...] any_2 ...) φ o)
   (any_1 ... [o ↦ φ any ...] any_2 ...)]
  [(Γ:: (any_1 ... [(acc_1 ... x) ↦ φ_k ...] any_2 ...) φ (acc_2 ... x))
   ([(acc_2 ... x) ↦ φ] any_1 ... [(acc_1 ... x) ↦ φ_k ...] any_2 ...)])

;; keeps the path only when it's in given domain.
;; Otherwise defaults to second path (3rd argument)
(define-metafunction scpcf
  default-o : o {x ...} o -> o
  [(default-o (acc ... x) {z ... x y ...} o) (acc ... x)]
  [(default-o o any o_1) o_1])

;; applies accessor on path
(define-metafunction scpcf
  acc-o : acc o -> o
  [(acc-o acc ∅) ∅]
  [(acc-o acc (acc_1 ... x)) (acc acc_1 ... x)])

;; removes element from given list/set
(define-metafunction scpcf
  del : (any ...) any ... -> (any ...)
  [(del {any_1 ... any any_2 ...} any_3 ... any any_4 ...)
   (del {any_1 ... any_2 ...} any_3 ... any any_4 ...)]
  [(del any any_1 ...) any])

;; interprets primitive ops
(define-metafunction scpcf
  δ : op (V o) ... Γ -> {(Ans Γ o) ...}
  
  ; add1
  [(δ add1 ((n ρ O ψ) o) Γ) {((,(add1 (term n)) [] [] []) Γ ∅)}]
  [(δ add1 (((• CC ...) ρ O ψ) o) Γ)
   ,(match (term (⊢? (CC ...) Γ o int?))
      ['Proved (term {(((• ,C/INT) [] [] []) Γ ∅)})]
      ['Refuted (term {(ERR Γ ∅)})]
      ['Neither (term {(((• ,C/INT) [] [] []) (Γ:: Γ int? o) ∅)
                       (ERR Γ ∅)})])]
  [(δ add1 (V o) Γ) {(ERR Γ ∅)}]
  
  ; sub1
  [(δ sub1 ((n ρ O ψ) o) Γ) {((,(sub1 (term n)) [] [] []) Γ ∅)}]
  [(δ sub1 (((• CC ...) ρ O ψ) o) Γ)
   ,(match (term (⊢? (CC ...) Γ o int?))
      ['Proved (term {(((• ,C/INT) [] [] []) Γ ∅)})]
      ['Refuted (term {(ERR Γ ∅)})]
      ['Neither (term {(((• ,C/INT) [] [] []) (Γ:: Γ int? o) ∅)
                       (ERR Γ ∅)})])]
  [(δ sub1 (V o) Γ) {(ERR Γ ∅)}]
  
  ; str-len
  [(δ str-len ((s ρ O ψ) o) Γ) {((,(string-length (term s)) [] [] []) Γ o)}]
  [(δ str-len (((• CC ...) ρ O ψ) o) Γ)
   ,(match (term (⊢? (CC ...) Γ o str?))
      ['Proved (term {(((• ,C/INT) [] [] []) Γ ∅)})]
      ['Refuted (term {(ERR Γ ∅)})]
      ['Neither (term {(((• ,C/INT) [] [] []) (Γ:: Γ str? o) ∅)
                       (ERR Γ ∅)})])]
  [(δ str-len (V o) Γ) {(ERR Γ ∅)}]
  
  ; car, cdr
  [(δ car (V o) Γ)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V1 (Γ:: Γ cons? o) (acc-o car o)))]
       [`() (term (ERR Γ ∅))])
     (term (split-cons (V o) Γ)))]
  [(δ cdr (V o) Γ)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V2 (Γ:: Γ cons? o) (acc-o cdr o)))]
       [`() (term (ERR Γ ∅))])
     (term (split-cons (V o) Γ)))]
  
  ; +
  [(δ + ((m ρ_m O_m ψ_m) o_m) ((n ρ_n O_n ψ_n) o_n) Γ)
   {((,(+ (term m) (term n)) [] [] []) Γ ∅)}]
  [(δ + (((• CC ...) ρ_m O_m ψ_m) o_m) ((n ρ_n O_n ψ_n) o_n) Γ)
   (δ + (((• CC ...) [] [] []) o_m) (((• ,C/INT) [] [] []) o_n) Γ)]
  [(δ + ((m ρ_m O_m ψ_m) o_m) (((• CC ...) ρ_n O_n ψ_n) o_n) Γ)
   (δ + (((• ,C/INT) [] [] []) o_m) (((• CC ...) [] [] []) o_n) Γ)]
  [(δ + (((• CC_1 ...) ρ_m O_m ψ_m) o_m) (((• CC_2 ...) ρ_n O_n ψ_n) o_n) Γ)
   ,(match (term ((⊢? (CC_1 ...) Γ o_m int?) (⊢? (CC_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {(ERR Γ ∅)})]
      [_ (term {(((• ,C/INT) [] [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                (ERR Γ ∅)})])]
  
  ; -
  [(δ - ((m ρ_m O_m ψ_m) o_m) ((n ρ_n O_n ψ_n) o_n) Γ)
   {((,(- (term m) (term n)) [] [] []) Γ ∅)}]
  [(δ - (((• CC ...) ρ_m O_m ψ_m) o_m) ((n ρ_n O_n ψ_n) o_n) Γ)
   (δ - (((• CC ...) [] [] []) o_m) (((• ,C/INT) [] [] []) o_n) Γ)]
  [(δ - ((m ρ_m O_m ψ_m) o_m) (((• CC ...) ρ_n O_n ψ_n) o_n) Γ)
   (δ - (((• ,C/INT) [] [] []) o_m) (((• CC ...) [] [] []) o_n) Γ)]
  [(δ - (((• CC_1 ...) ρ_m O_m ψ_m) o_m) (((• CC_2 ...) ρ_n O_n ψ_n) o_n) Γ)
   ,(match (term ((⊢? (CC_1 ...) Γ o_m int?) (⊢? (CC_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {(ERR Γ ∅)})]
      [_ (term {(((• ,C/INT) [] [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                (ERR Γ ∅)})])]
  
  ; *
  [(δ * ((m ρ_m O_m ψ_m) o_m) ((n ρ_n O_n ψ_n) o_n) Γ)
   {((,(* (term m) (term n)) [] [] []) Γ ∅)}]
  [(δ * (((• CC ...) ρ_m O_m ψ_m) o_m) ((n ρ_n O_n ψ_n) o_n) Γ)
   (δ * (((• CC ...) [] [] []) o_m) (((• ,C/INT) [] [] []) o_n) Γ)]
  [(δ * ((m ρ_m O_m ψ_m) o_m) (((• CC ...) ρ_n O_n ψ_n) o_n) Γ)
   (δ * (((• ,C/INT) [] [] []) o_m) (((• CC ...) [] [] []) o_n) Γ)]
  [(δ * (((• CC_1 ...) ρ_m O_m ψ_m) o_m) (((• CC_2 ...) ρ_n O_n ψ_n) o_n) Γ)
   ,(match (term ((⊢? (CC_1 ...) Γ o_m int?) (⊢? (CC_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {(ERR Γ ∅)})]
      [_ (term {(((• ,C/INT) [] [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                (ERR Γ ∅)})])]
  
  ; cons
  [(δ cons (V_1 o_1) (V_2 o_2) Γ) {((Cons V_1 V_2) Γ ∅)}]
  
  ; predicates
  [(δ tt (V o) Γ) {((#t [] [] []) Γ ∅)}]
  [(δ p? (((• CC ...) ρ O ψ) o) Γ)
   ,(match (term (⊢? (CC ...) Γ o p?))
      ['Proved (term {((#t [] [] []) (Γ:: Γ p? o) ∅)})]
      ['Refuted (term {((#f [] [] []) (Γ:: Γ (¬ p?) o) ∅)})]
      ['Neither (term {((#t [] [] []) (Γ:: Γ p? o) ∅)
                       ((#f [] [] []) (Γ:: Γ (¬ p?) o) ∅)})])]
  [(δ p? (V o) Γ)
   ,(match (term (concrete-check p? V))
      [#t (term {((#t [] [] []) (Γ:: Γ p? o) ∅)})]
      [#f (term {((#f [] [] []) (Γ:: Γ (¬ p?) o) ∅)})])]
  
  [(δ op (V o) ... Γ) {(ERR Γ ∅)}])

;; split pair closure into 2, or () indicating not a pair
(define-metafunction scpcf
  split-cons : (V o) Γ -> {(V ...) ...} ; (V ...) being (V V) or ()
  [(split-cons ((Cons V_1 V_2) o) Γ) {(V_1 V_2)}]
  [(split-cons (((• CC ...) ρ O ψ) o) Γ)
   ,(match (term (acc-cons (CC ...) ()))
      ['() (match (term (Γ⊢? Γ o cons?))
             ['Proved (term { (((•) [] [] []) ((•) [] [] [])) })]
             ['Refuted (term {()})]
             ['Neither (term { (((•) [] [] []) ((•) [] [] []))
                               () })])]
      [acc (s-map
            (match-lambda
              [`(,Cs1 ,Cs2) (term (((• ,@ Cs1) [] [] []) ((• ,@ Cs2) [] [] [])))]
              ['() (term ())])
            acc)])]
  [(split-cons (V o) Γ) {()}])
(define-metafunction scpcf
  acc-cons : (CC ...) {((CC ...) ...) ...} -> {((CC ...) ...) ...}
  [(acc-cons () any) any]
  [(acc-cons ([(or/c c_1 c_2) ρ O ψ] any ...) any_acc)
   ,(∪ (term (acc-cons ((c_1 ρ O ψ) any ...) any_acc))
       (term (acc-cons ((c_2 ρ O ψ) any ...) any_acc)))]
  [(acc-cons ([(and/c c_1 c_2) ρ O ψ] any ...) any_acc)
   (acc-cons ([c_1 ρ O ψ] [c_2 ρ O ψ] any ...) any_acc)]
  [(acc-cons ([(c ↦ any ...) ρ O ψ] any_1 ...) any_acc) '(())]
  [(acc-cons ([(cons/c c_1 c_2) ρ O ψ] any ...) any_acc)
   (acc-cons (any ...)
             ,(match (term any_acc)
                ['() (term {([(c_1 ρ O ψ)] [(c_2 ρ O ψ)])})]
                [_ (s-map
                    (match-lambda
                      [`(,D1 ,D2) (term (([c_1 ρ O ψ] ,@ D1) ([c_2 ρ O ψ] ,@ D2)))]
                      ['() (term ())])
                    (term any_acc))]))]
  [(acc-cons ([x ρ O ψ] any ...) any_acc) (acc-cons ([! ρ x] any ...) any_acc)]
  [(acc-cons ([(μ (x) c) ρ O ψ] any ...) any_acc)
   (acc-cons ((c (:: ρ [x ↦ ((μ (x) c) ρ O ψ)]) (:: O [x ↦ x])) any ...) any_acc)]
  [(acc-cons ([(flat p?) ρ O ψ] any ...) any_acc)
   (acc-cons (any ...) ,(match (term any_acc)
                          ['() '([() ()])]
                          [x x]))
   (where #t (implies? p? cons?))]
  [(acc-cons ([(flat p?) ρ O ψ] any ...) any_acc)
   '()
   (where #t (excludes? p? cons?))]
  [(acc-cons (any any_1 ...) any_acc) (acc-cons (any_1 ...) any_acc)])

(define-metafunction scpcf
  subst : e x any -> e
  [(subst (λ (x) e) x any) (λ (x) e)]
  [(subst (λ (z) e) x any) (λ (z) (subst e x any))]
  [(subst (μ (x) e) x any) (μ (x) e)]
  [(subst (μ (z) e) x any) (μ (z) (subst e x any))]
  [(subst x x any) any]
  [(subst x z any) x]
  [(subst (e ...) x any) ((subst e x any) ...)]
  [(subst (mon c e) x any)
   (subst (mon (subst-c c x any) (subst e x any)))]
  [(subst (let [x e_1] e) x any) (let [x (subst e_1 x any)] e)]
  [(subst (let [z e_1] e) x any) (let [z (subst e_1 x any)] (subst e x any))]
  [(subst (let ([z e_z] ...) e) x any)
   (let ([z (subst e_z x any)] ...) e)
   (where (any_2 ... x any_3 ...) (z ...))]
  [(subst (let ([z e_z] ...) e) x any)
   (let ([z (subst e_z x any)] ...) (subst e x any))]
  [(subst (cond [e_1 e_2] ... [else e]) x any)
   (cond [(subst e_1 x any) (subst e_2 x any)] ... [else (subst e x any)])]
  [(subst (any_l e ...) x any) (any_l (subst e x any) ...)]
  [(subst v x any) v]
  [(subst blame x any) blame])
(define-metafunction scpcf
  subst-c : c x any -> c
  [(subst-c (flat e) x any) (flat (subst e x any))]
  [(subst-c (c_1 ↦ (λ (x) c_2)) x any)
   ((subst-c c_1 x any) ↦ (λ (x) c_2))]
  [(subst-c (c_1 ↦ (λ (z) c_2)) x any)
   ((subst-c c_1 x any) ↦ (λ (z) (subst-c c_2 x any)))]
  [(subst-c (μ (x) c) x any) (μ (x) c)]
  [(subst-c (μ (z) c) x any) (μ (z) (subst-c c x any))]
  [(subst-c (any_l c ...) x any) (any_l (subst-c c x any) ...)])


;;;;; HELPER stuff for non-determinism

;; kills duplicates
;; rem-dup : [Listof X] -> [Listof X]
(define rem-dup (compose set->list list->set))

;; like map, but kills duplicates
;; s-map : [X -> Y] [Listof X] -> [Listof Y]
(define (s-map f xs)
  (rem-dup (map f xs)))

;; non-det : [X -> [Listof Y]] [Listof X] -> [Listof Y]
#;(define (non-det f xs)
  (rem-dup (apply append (map f xs))))

;; ∪ : [Listof X] [Listof X] -> [Listof X]
(define (∪ xs ys)
  (rem-dup (append xs ys)))

#;(define-syntax non-det:
  (syntax-rules (← return:)
    [(_ [V Γ o ← e] e1 e2 ...)
     (non-det
      (match-lambda
        [`(,V ,Γ ,o) (non-det: e1 e2 ...)]
        ['ERR '{ERR}])
      e)]
    [(_ e1 e2 e3 ...) (non-det (λ (_) (non-det: e2 e3 ...))
                               e1)]
    [(_ (return: x ...)) (rem-dup (list x ...))]
    [(_ e) e]))