#lang racket
(require redex)
(require "lang-simple.rkt")

(provide
 scpcf δ ev step
 default-o acc-o subst subst-c FC var-not-in
 flush pop push mk-Γ upd-Γ dom :: Γ:: ! FC split-cons var-from-path
 refine-v refine-with-Γ
 s-map rem-dup non-det:
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
  [b .... s (• D ...)]
  [bool #t #f]
  [s string]
  [ψ p? (¬ p?)]
  
  ; environments
  [O ([x ↦ o′] ...)]
  [Γ ([o′ ↦ ψ ...] ...)]
  
  ; path
  [o ∅ o′]
  [o′ (acc ... x)]
  [acc car cdr]
  
  ; closures
  [C (e ρ O)]
  [V (v ρ O)
     (Cons V V)]
  [D (c ρ O)]
  
  ; big-step answer
  [A (V Γ o) ERR]
  ; interpreter answer
  [ea n s bool function • (• p? ...) ERR (cons ea ea)]
  
  ; verification answer
  [Verified? Proved Refuted Neither])

(define c/any (term (flat tt)))
(define C/ANY (term (,c/any [] [])))
(define c/int (term (flat int?)))
(define C/INT (term (,c/int [] [])))
(define c/str (term (flat str?)))
(define C/STR (term (,c/str [] [])))
(define c/bool (term (flat bool?)))
(define C/BOOL (term (,c/bool [] [])))

(define-metafunction scpcf
  ; assume all variables have been (statically) renamed
  ev : e -> {ea ...}
  [(ev e)
   ,(rem-dup (term ((simplify A) ...)))
   (where (A ...) (step [] [] [] e))])

(define-metafunction scpcf
  simplify : A -> ea
  [(simplify ERR) ERR]
  [(simplify (((λ (x) e) ρ O) Γ o)) function]
  [(simplify ((op ρ O) Γ o)) function]
  [(simplify (((• D ...) ρ O) Γ o)) ,(match (rem-dup (term (all-preds (D ...))))
                                       ['() (term •)]
                                       [ps (term (• ,@ ps))])]
  [(simplify ((Cons V_1 V_2) Γ o))
   (cons (simplify (V_1 [] ∅)) (simplify (V_2 [] ∅)))]
  [(simplify ((any ρ O) Γ o)) any])

(define-metafunction scpcf
  all-preds : (D ...) -> (p? ...)
  [(all-preds (((flat tt) ρ O) any ...)) (all-preds (any ...))]
  [(all-preds (((flat p?) ρ O) any ...))
   ,(cons (term p?) (term (all-preds (any ...))))]
  [(all-preds (any any_1 ...)) (all-preds (any_1 ...))]
  [(all-preds ()) ()])

(define-metafunction scpcf
  step : Γ ρ O e -> {A ...}
  
  ; desugar
  [(step Γ ρ O (and e)) (step Γ ρ O e)]
  [(step Γ ρ O (and e_1 e ...)) (step Γ ρ O (if e_1 (and e ...) #f))]
  [(step Γ ρ O (or e)) (step Γ ρ O e)]
  [(step Γ ρ O (or e_1 e ...))
   (step Γ ρ O (let (tmp e_1) (if tmp tmp (or e ...))))
   (where tmp ,(variable-not-in (term (e ...)) (term tmp)))]
  [(step Γ ρ O (let (x e_x) e)) (step Γ ρ O ((λ (x) e) e_x))]
  [(step Γ ρ O (let ([x e_x]) e)) (step Γ ρ O ((λ (x) e) e_x))]
  [(step Γ ρ O (let ([x e_x] [y e_y] ...) e))
   (step Γ ρ O (let (x e_x) (let ([y e_y] ...) e)))]
  [(step Γ ρ O (cond [else e])) (step Γ ρ O e)]
  [(step Γ ρ O (cond [e_1 e_2] any ...))
   (step Γ ρ O (if e_1 e_2 (cond any ...)))]
  [(step Γ ρ O (begin e)) (step Γ ρ O e)]
  [(step Γ ρ O (begin e_1 e_2 ...))
   (step Γ ρ O (let (tmp e_1) (begin e_2 ...)))
   (where tmp ,(variable-not-in (term (e_2 ...)) (term tmp)))]
  [(step Γ ρ O •) (step Γ ρ O (•))]
  
  ; blame
  [(step Γ ρ O blame) {ERR}]
  
  ; val
  [(step Γ ρ O v) {((v [flush Γ ρ] O) Γ ∅)}]
  
  ; var
  [(step Γ ρ O x) {((refine-with-Γ [! ρ x] Γ [! O x]) Γ (! O x))}]
  
  ; app-1
  [(step Γ ρ O (e_f e_x))
   ,(non-det:
     [Vf Γ1 __ ← (term (step Γ ρ O e_f))]
     [Vx Γ2 ox ← (term (step ,Γ1 ρ O e_x))]
     (match Vf
       [`((λ (,x) ,ey) ,ρλ ,Oλ)
        (non-det:
         [Vy Γ3 oy ← (term (step [push (mk-Γ (dom ,ρλ) ,Γ2) ,x]
                                 [:: ,ρλ [,x ↦ ,Vx]]
                                 [:: ,Oλ [,x ↦ (default-o ,ox (dom ,ρλ) (,x))]]
                                 ,ey))]
         [return: (term (,Vy [upd-Γ ,Γ2 (pop ,Γ3 ,x)]
                             [default-o ,oy (dom [pop Γ ,x]) ∅]))])]
       [`((• ,D ...) ,_ρ ,_O) (term {ERR
                                     (((• ,@ (term (D-ranges ,@ D))) [] []) ,Γ2 ∅)})]
       [`(,o1 ,_ρ ,_O) (term (δ ,o1 (,Vx ,ox) ,Γ2))]))]
  ; app-2
  [(step Γ ρ O (e_f e_1 e_2))
   ,(non-det:
     [`(,o2 ,_ρ ,_O) Γ1 __ ← (term (step Γ ρ O e_f))]
     [Vx Γ2 ox ← (term (step ,Γ1 ρ O e_1))]
     [Vy Γ3 oy ← (term (step ,Γ2 ρ O e_2))]
     [term (δ ,o2 (,Vx ,ox) (,Vy ,oy) ,Γ3)])]
  
  ; if
  [(step Γ ρ O (if e_1 e_2 e_3))
   ,(non-det:
     [V1 Γ1 o1 ← (term (step Γ ρ O e_1))]
     [`(,t? ,_ρ ,_O) Γt ot ← (term (δ true? (,V1 ,o1) ,Γ1))]
     [if t?
         (term (step ,Γt ρ O e_2))
         (term (step ,Γt ρ O e_3))])]
  
  ; μ
  [(step Γ ρ O (μ (x) e)) (step Γ ρ O (subst e x (μ (x) e)))]
  
  ; mon-flat
  [(step Γ ρ O (mon [flat e_p] e))
   (step Γ ρ O (let [x e] (if (e_p x) x blame)))
   (where x ,(variable-not-in (term e_p) (term x)))]
  ; mon-and
  [(step Γ ρ O (mon [and/c c_1 c_2] e))
   (step Γ ρ O (mon c_2 (mon c_1 e)))]
  ; mon-or
  [(step Γ ρ O (mon (or/c c_1 c_2) e))
   (step Γ ρ O (let [x e] (if ([FC c_1] x) x (mon c_2 x))))]
  ; mon-cons
  [(step Γ ρ O (mon (cons/c c_1 c_2) e))
   (step Γ ρ O (let [x (mon (flat cons?) e)]
                 (cons (mon c_1 (car x)) (mon c_2 (cdr x)))))]
  ; mon-μ
  [(step Γ ρ O (mon (μ (x) c) e)) (step Γ ρ O (mon (subst-c c x (μ (x) c)) e))]
  ; mon-fun
  [(step Γ ρ O (mon (c_1 ↦ (λ (x) c_2)) e))
   (step Γ ρ O (let [f e] (λ (x) (mon c_2 (f (mon c_1 x))))))
   (where f ,(variable-not-in (term (c_1 x c_2)) (term f)))])


;; extract function contract's domain
(define-metafunction scpcf
  D-ranges : (D ...) -> (D ...)
  [(D-ranges ()) ()]
  [(D-ranges (((c_1 ↦ (λ (x) c_2)) ρ O) any ...))
   ,(cons (term (c_2 (:: ρ [x ↦ ((•) [] [])])
                     (:: O [x ↦ x])))
          (term (D-ranges (any ...))))]
  [(D-ranges (any_1 any ...)) (D-ranges (any ...))])

;; 'flushes' all propositions in Γ into ρ as refinining contracts for •'s
(define-metafunction scpcf
  flush : Γ ρ -> ρ
  [(flush [] ρ) ρ]
  [(flush ([x ↦ ψ ...] any ...) (any_1 ... [x ↦ ((• D ...) ρ O)] any_2 ...))
   (flush (any ...)
          (any_1 ... [x ↦ ((• (mk-D () ψ) ... D ...) [] [])] any_2 ...))]
  [(flush ([(acc ... x) ↦ ψ ...] any ...)
          (any_1 ... [x ↦ ((• D ...) ρ O)] any_2 ...))
   (flush (any ...)
          (any_1 ... [x ↦ ((• (mk-D (acc ...) ψ) ... D ...) [] [])] any_2 ...))]
  [(flush (any_1 any ...) ρ) (flush (any ...) ρ)])

;; check whether value satisfies contract
(define-metafunction scpcf
  V⊢? : V D -> Verified?
  [(V⊢? ((• any_1 ... D any_2 ...) ρ O) D_1)
   Proved
   (where #t (D-implies? D D_1))]
  [(V⊢? ((• any_1 ... D any_2 ...) ρ O) D_1)
   Refuted
   (where #t (D-excludes? D D_1))]
  [(V⊢? V D) Neither])

;; uses existing information to check whether the predicate holds
(define-metafunction scpcf
  ⊢? : (D ...) Γ o p? -> Verified?
  ; Γ is easier/cheaper, so use it first
  [(⊢? (D ...) Γ o p?) ,(match (term (Γ⊢? Γ o p?))
                          ['Proved (term Proved)]
                          ['Refuted (term Refuted)]
                          ['Neither (term (C⊢? (D ...) p?))])])

;; checks whether contract set can prove/refute predicate
(define-metafunction scpcf
  C⊢? : (D ...) p? -> Verified?
  [(C⊢? (any_1 ... ((flat p?) ρ O) any_2 ...) p?_1)
   Proved
   (where #t (implies? p? p?_1))]
  [(C⊢? (any_1 ... ((flat p?) ρ O) any_2 ...) p?_1)
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
  [(concrete-check int? (n ρ O)) #t]
  [(concrete-check zero? (0 ρ O)) #t]
  [(concrete-check str? (s ρ O)) #t]
  [(concrete-check false? (#f ρ O)) #t]
  [(concrete-check false? V) #f]
  [(concrete-check bool? (bool ρ O)) #t]
  [(concrete-check proc? ((λ (x) e) ρ O)) #t]
  [(concrete-check true? (#f ρ O)) #f]
  [(concrete-check true? V) #t]
  [(concrete-check cons? (Cons V_1 V_2)) #t]
  [(concrete-check p? V) #f])

;; refines value with given (closed) contract
(define-metafunction scpcf
  refine-v : V D -> {V ...}
  [(refine-v ((• D_1 ...) ρ O) D)
   ,(s-map
     (λ (Cs) (term ((• ,@ Cs) ρ O)))
     (term (refine (D_1 ...) D)))]
  [(refine-v V D) {V}])

;; refines set of contracts with another contract
(define-metafunction scpcf
  refine : {D ...} D -> {{D ...} ...}
  
  ; special cases where we can do something smarter
  [(refine {any_1 ... D_1 any_2 ...} D_2)
   {{any_1 ... D_1 any_2 ...}}
   (where #t (D-implies? D_1 D_2))] ; refining contract is redundant
  [(refine {any_1 ... D_1 any_2 ...} D_2)
   {{any_1 ... D_2 any_2 ...}}
   (where #t (D-implies? D_2 D_1))] ; one of the old contract is redundant
  [(refine {any_1 ... D_1 any_2 ...} D_2)
   {}
   (where #t (D-excludes? D_1 D_2))] ; the refinement is bullshit
  
  ; general cases
  [(refine any ((or/c c_1 c_2) ρ O)) ; split disjunction for better precision
   ,(∪ (term (refine any (c_1 ρ O))) (term (refine any (c_2 ρ O))))]
  [(refine any ((and/c c_1 c_2) ρ O)) ; break conjunction into smaller refinements
   ,(s-map
     (λ (Cs)
       (term (refine ,Cs (c_2 ρ O))))
     (term (refine any (c_2 ρ O))))]
  [(refine any ((μ (x) c) ρ O)) ; unroll recursive contract
   (refine any (c (:: [x ↦ ((μ (x) c) ρ O)] ρ)
                  (:: [x ↦ x] O)))]
  [(refine any (x ρ O)) (refine any (! ρ x))]
  [(refine {D ...} D_1) {{D_1 D ...}}])

;; checks whether first contract (definitely) implies second
;; may give false negative
(define-metafunction scpcf
  D-implies? : D D -> bool
  [(D-implies? ((flat p?) ρ O) ((flat p?_1) ρ_1 O_1)) (implies? p? p?_1)]
  [(D-implies? D_1 D_2) #f])

;; checks whether first contract (definitely) contradicts second
;; may give false negative
(define-metafunction scpcf
  D-excludes? : D D -> bool
  [(D-excludes? ((flat p?) ρ O) ((flat p?_1) ρ_1 O_1)) (excludes? p? p?_1)]
  [(D-excludes? D_1 D_2) #f])

;; checks whether first proposition (definitely) implies second
(define-metafunction scpcf
  ψ-implies? : ψ ψ -> bool
  [(ψ-implies? p? p?_1) (implies? p? p?_1)]
  [(ψ-implies? (¬ p?) (¬ p?_1)) (implies? p?_1 p?)]
  [(ψ-implies? p? (¬ p?_1)) (excludes? p? p?_1)]
  [(ψ-implies? (¬ true?) false?) #t]
  [(ψ-implies? (¬ false? true?)) #t]
  [(ψ-implies? (¬ p?) p?_1) #f])

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
  refine-with-Γ : V Γ o′ -> V
  [(refine-with-Γ ((• D ...) ρ O) ([(acc ... acc_1 ... x) ↦ ψ ...] any ...) (acc_1 ... x))
   (refine-with-Γ ((• (mk-D (acc ...) ψ) ... D ...) ρ O) (any ...) (acc_1 ... x))]
  [(refine-with-Γ ((• D ...) ρ O) (any any_1 ...) o′)
   (refine-with-Γ ((• D ...) ρ O) (any_1 ...) o′)]
  [(refine-with-Γ V Γ o′) V])

;; makes (closed) contract out of proposition
(define-metafunction scpcf
  mk-D : (acc ...) ψ -> D
  [(mk-D any p?) ((mk-c any (flat p?)) [] [])]
  ; lose precision for now until we have not/c?
  [(mk-D any (¬ p?)) ((flat tt) [] [])])
;; constructs contract for given path of accessors
(define-metafunction scpcf
  mk-c : (acc ...) c -> c
  [(mk-c () c) c]
  [(mk-c (car acc ...) c) (mk-c (acc ...) (cons/c c ,c/any))]
  [(mk-c (cdr acc ...) c) (mk-c (acc ...) (cons/c ,c/any c))])

;; removes x from Γ's domain
(define-metafunction scpcf
  pop : Γ x -> Γ
  [(pop () x) ()]
  [(pop ([x ↦ any ...] any_1 ...) x) (pop (any_1 ...) x)]
  [(pop ([(any_acc ... x) ↦ any ...] any_1 ...) x) (pop (any_1 ...) x)]
  [(pop (any any_1 ...) x) ,(cons (term any) (term (pop (any_1 ...) x)))])

;; overrides Γ with [x ↦ tt]
(define-metafunction scpcf
  push : Γ x -> Γ
  [(push Γ x) ,(cons (term [(x) ↦ tt]) (term (pop Γ x)))])

;; returns environment's domain. (overloaded on closures)
(define-metafunction scpcf
  dom : any -> {x ...}
  [(dom ([o′ ↦ any ...] ...)) ,(rem-dup (term ((var-from-path o′) ...)))]
  [(dom ([x ↦ any ...] ...)) (x ...)]
  ; overloaded
  [(dom (e ρ O)) (dom ρ)]
  [(dom (mon (c ρ O) (C o))) (dom ρ)])
;; extracts variable from path
(define-metafunction scpcf
  var-from-path : o′ -> x
  [(var-from-path (any ... x)) x])

;; makes proposition environment with given domain and updates it with Γ
(define-metafunction scpcf
  mk-Γ : {x ...} Γ -> Γ
  [(mk-Γ {x ...} Γ) (upd-Γ ([(x) ↦ tt] ...) Γ)])

;; updates Γ1 with propositions from Γ2 if they talk about the same variable
(define-metafunction scpcf
  upd-Γ : Γ Γ -> Γ
  [(upd-Γ any []) any]
  [(upd-Γ (any_1 ... [o′ ↦ ψ ...] any_2 ...) ([o′ ↦ ψ_1 ...] any_3 ...))
   (upd-Γ (any_1 ... [o′ ↦ ψ_1 ...] any_2 ...) (any_3 ...))]
  [(upd-Γ (any_1 ... [(acc_1 ... x) ↦ ψ ...] any_2 ...)
          ([(acc ... x) ↦ ψ_1 ...] any_3 ...))
   (upd-Γ ([(acc ... x) ↦ ψ_1 ...] any_1 ... [(acc_1 ... x) ↦ ψ ...] any_2 ...)
          (any_3 ...))]
  [(upd-Γ any (any_1 any_2 ...)) (upd-Γ any (any_2 ...))])

;; updates proposition environment with proposition
(define-metafunction scpcf
  Γ:: : Γ ψ o -> Γ
  [(Γ:: any_Γ any_ψ ∅) any_Γ]
  [(Γ:: (any ... [o ↦ tt] any_1 ...) ψ o) (any ... [o ↦ ψ] any_1 ...)]
  [(Γ:: (any ... [o ↦ ψ_1 ... ψ ψ_n ...] any_1 ...) ψ o)
   (any ... [o ↦ ψ_1 ... ψ ψ_n ...] any_1 ...)]
  [(Γ:: (any_1 ... [o ↦ any ...] any_2 ...) ψ o)
   (any_1 ... [o ↦ ψ any ...] any_2 ...)]
  [(Γ:: (any_1 ... [o_k ↦ ψ_k ...] any_2 ...) ψ o)
   ([o ↦ ψ] any_1 ... [o_k ↦ ψ_k ...] any_2 ...)
   (where (x x) ((var-from-path o_k) (var-from-path o)))])

;; keeps the path only when it's in given domain
(define-metafunction scpcf
  default-o : o {x ...} o -> o
  [(default-o ∅ any o) o]
  [(default-o x {z ... x y ...} any) x]
  [(default-o (acc ... x) {z ... x y ...} any) (acc ... x)]
  [(default-o o any o_1) o_1])

;; applies accessor on path
(define-metafunction scpcf
  acc-o : acc o -> o
  [(acc-o acc ∅) ∅]
  [(acc-o acc x) (acc x)]
  [(acc-o acc (acc_1 ... x)) (acc acc_1 ... x)])

;; interprets primitive ops
(define-metafunction scpcf
  δ : op (V o) ... Γ -> {A ...}
  
  ; add1
  [(δ add1 ((n ρ O) o) Γ) {((,(add1 (term n)) [] []) Γ ∅)}]
  [(δ add1 (((• D ...) ρ O) o) Γ)
   ,(match (term (⊢? (D ...) Γ o int?))
      ['Proved (term {(((• ,C/INT) [] []) Γ ∅)})]
      ['Refuted (term {ERR})]
      ['Neither (term {(((• ,C/INT) [] []) (Γ:: Γ int? o) ∅)
                       ERR})])]
  [(δ add1 (V o) Γ) {ERR}]
  
  ; sub1
  [(δ sub1 ((n ρ O) o) Γ) {((,(sub1 (term n)) [] []) Γ ∅)}]
  [(δ sub1 (((• D ...) ρ O) o) Γ)
   ,(match (term (⊢? (D ...) Γ o int?))
      ['Proved (term {(((• ,C/INT) [] []) Γ ∅)})]
      ['Refuted (term {ERR})]
      ['Neither (term {(((• ,C/INT) [] []) (Γ:: Γ int? o) ∅)
                       ERR})])]
  [(δ sub1 (V o) Γ) {ERR}]
  
  ; str-len
  [(δ str-len ((s ρ O) o) Γ) {((,(string-length (term s)) [] []) Γ o)}]
  [(δ str-len (((• D ...) ρ O) o) Γ)
   ,(match (term (⊢? (D ...) Γ o str?))
      ['Proved (term {(((• ,C/INT) [] []) Γ ∅)})]
      ['Refuted (term {ERR})]
      ['Neither (term {(((• ,C/INT) [] []) (Γ:: Γ str? o) ∅)
                       ERR})])]
  [(δ str-len (V o) Γ) {ERR}]
  
  ; car, cdr
  [(δ car (V o) Γ)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V1 (Γ:: Γ cons? o) (acc-o car o)))]
       [`() (term ERR)])
     (term (split-cons (V o) Γ)))]
  [(δ cdr (V o) Γ)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V2 (Γ:: Γ cons? o) (acc-o cdr o)))]
       [`() (term ERR)])
     (term (split-cons (V o) Γ)))]
  
  ; +
  [(δ + ((m ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   {((,(+ (term m) (term n)) [] []) Γ ∅)}]
  [(δ + (((• D ...) ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   (δ + (((• D ...) [] []) o_m) (((• ,C/INT) [] []) o_n) Γ)]
  [(δ + ((m ρ_m O_m) o_m) (((• D ...) ρ_n O_n) o_n) Γ)
   (δ + (((• ,C/INT) [] []) o_m) (((• D ...) [] []) o_n) Γ)]
  [(δ + (((• D_1 ...) ρ_m O_m) o_m) (((• D_2 ...) ρ_n O_n) o_n) Γ)
   ,(match (term ((⊢? (D_1 ...) Γ o_m int?) (⊢? (D_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERR})]
      [_ (term {(((• ,C/INT) [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                ERR})])]
  
  ; -
  [(δ - ((m ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   {((,(- (term m) (term n)) [] []) Γ ∅)}]
  [(δ - (((• D ...) ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   (δ - (((• D ...) [] []) o_m) (((• ,C/INT) [] []) o_n) Γ)]
  [(δ - ((m ρ_m O_m) o_m) (((• D ...) ρ_n O_n) o_n) Γ)
   (δ - (((• ,C/INT) [] []) o_m) (((• D ...) [] []) o_n) Γ)]
  [(δ - (((• D_1 ...) ρ_m O_m) o_m) (((• D_2 ...) ρ_n O_n) o_n) Γ)
   ,(match (term ((⊢? (D_1 ...) Γ o_m int?) (⊢? (D_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERR})]
      [_ (term {(((• ,C/INT) [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                ERR})])]
  
  ; *
  [(δ * ((m ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   {((,(* (term m) (term n)) [] []) Γ ∅)}]
  [(δ * (((• D ...) ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   (δ * (((• D ...) [] []) o_m) (((• ,C/INT) [] []) o_n) Γ)]
  [(δ * ((m ρ_m O_m) o_m) (((• D ...) ρ_n O_n) o_n) Γ)
   (δ * (((• ,C/INT) [] []) o_m) (((• D ...) [] []) o_n) Γ)]
  [(δ * (((• D_1 ...) ρ_m O_m) o_m) (((• D_2 ...) ρ_n O_n) o_n) Γ)
   ,(match (term ((⊢? (D_1 ...) Γ o_m int?) (⊢? (D_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERR})]
      [_ (term {(((• ,C/INT) [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                ERR})])]
  
  ; cons
  [(δ cons (V_1 o_1) (V_2 o_2) Γ) {((Cons V_1 V_2) Γ ∅)}]
  
  ; predicates
  [(δ tt (V o) Γ) {((#t [] []) Γ ∅)}]
  [(δ p? (((• D ...) ρ O) o) Γ)
   ,(match (term (⊢? (D ...) Γ o p?))
      ['Proved (term {((#t [] []) (Γ:: Γ p? o) ∅)})]
      ['Refuted (term {((#f [] []) (Γ:: Γ (¬ p?) o) ∅)})]
      ['Neither (term {((#t [] []) (Γ:: Γ p? o) ∅)
                       ((#f [] []) (Γ:: Γ (¬ p?) o) ∅)})])]
  [(δ p? (V o) Γ)
   ,(match (term (concrete-check p? V))
      [#t (term {((#t [] []) (Γ:: Γ p? o) ∅)})]
      [#f (term {((#f [] []) (Γ:: Γ (¬ p?) o) ∅)})])]
  
  [(δ op (V o) ... Γ) {ERR}])

;; split pair closure into 2, or () indicating not a pair
(define-metafunction scpcf
  split-cons : (V o) Γ -> {(V ...) ...} ; (V ...) being (V V) or ()
  [(split-cons ((Cons V_1 V_2) o) Γ) {(V_1 V_2)}]
  [(split-cons (((• D ...) ρ O) o) Γ)
   ,(match (term (acc-cons (D ...) ()))
      ['() (match (term (Γ⊢? Γ o cons?))
             ['Proved (term { (((•) [] []) ((•) [] [])) })]
             ['Refuted (term {()})]
             ['Neither (term { (((•) [] []) ((•) [] []))
                               () })])]
      [acc (s-map
            (match-lambda
              [`(,Cs1 ,Cs2) (term (((• ,@ Cs1) [] []) ((• ,@ Cs2) [] [])))]
              ['() (term ())])
            acc)])]
  [(split-cons (V o) Γ) {()}])
(define-metafunction scpcf
  acc-cons : (D ...) {((D ...) ...) ...} -> {((D ...) ...) ...}
  [(acc-cons () any) any]
  [(acc-cons ([(or/c c_1 c_2) ρ O] any ...) any_acc)
   ,(∪ (term (acc-cons ((c_1 ρ O) any ...) any_acc))
       (term (acc-cons ((c_2 ρ O) any ...) any_acc)))]
  [(acc-cons ([(and/c c_1 c_2) ρ O] any ...) any_acc)
   (acc-cons ([c_1 ρ O] [c_2 ρ O] any ...) any_acc)]
  [(acc-cons ([(c ↦ any ...) ρ O] any_1 ...) any_acc) '(())]
  [(acc-cons ([(cons/c c_1 c_2) ρ O] any ...) any_acc)
   (acc-cons (any ...)
             ,(match (term any_acc)
                ['() (term {([(c_1 ρ O)] [(c_2 ρ O)])})]
                [_ (s-map
                    (match-lambda
                      [`(,D1 ,D2) (term (([c_1 ρ O] ,@ D1) ([c_2 ρ O] ,@ D2)))]
                      ['() (term ())])
                    (term any_acc))]))]
  [(acc-cons ([x ρ O] any ...) any_acc) (acc-cons ([! ρ x] any ...) any_acc)]
  [(acc-cons ([(μ (x) c) ρ O] any ...) any_acc)
   (acc-cons ((c (:: ρ [x ↦ ((μ (x) c) ρ O)]) (:: O [x ↦ x])) any ...) any_acc)]
  [(acc-cons ([(flat p?) ρ O] any ...) any_acc)
   (acc-cons (any ...) ,(match (term any_acc)
                          ['() '([() ()])]
                          [x x]))
   (where #t (implies? p? cons?))]
  [(acc-cons ([(flat p?) ρ O] any ...) any_acc)
   '()
   (where #t (excludes? p? cons?))]
  [(acc-cons (any any_1 ...) any_acc) (acc-cons (any_1 ...) any_acc)])



;;;;; HELPER stuff for non-determinism

;; kills duplicates
;; rem-dup : [Listof X] -> [Listof X]
(define rem-dup (compose set->list list->set))

;; like map, but kills duplicates
;; s-map : [X -> Y] [Listof X] -> [Listof Y]
(define (s-map f xs)
  (rem-dup (map f xs)))

;; non-det : [X -> [Listof Y]] [Listof X] -> [Listof Y]
(define (non-det f xs)
  (rem-dup (apply append (map f xs))))

;; ∪ : [Listof X] [Listof X] -> [Listof X]
(define (∪ xs ys)
  (rem-dup (append xs ys)))

(define-syntax non-det:
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