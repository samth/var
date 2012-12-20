#lang racket
(require redex)

(provide scpcf-src scpcf compile MON ⇓ ⇓a Γ-refine Γ-flush mk-φ REFINE close)

; source language
(define-language scpcf-src
  [e a
     x
     (e e e ...)
     (if e e e)
     (μ (x) e)
     (mon c e)
     (let [x e] e)]
  [a blame v]
  [v (λ (x) e) b •]
  [b integer #t #f o1 o2]
  [o1 p? add1 car cdr]
  [o2 + cons]
  [op o1 o2]
  [(m n) integer]
  [p? tt int? false? proc? cons?]
  [c (flat e)
     (c ↦ (λ (x) c))
     (or/c c c)
     (and/c c c)
     (cons/c c c)
     (μ (x) c)
     x]
  
  [Verified? Proved Refuted Neither]
  [(x y z f) variable-not-otherwise-mentioned])

; target language
(define-extended-language scpcf scpcf-src
  [e a
     x
     (e e e ...)
     (if e e e)
     (μ (x) e)
     (let [x e] e)
     (refine e e)]
  
  ; closure
  [C (e ρ O)]
  [V ((λ (x) e) ρ O) b (• P? ...) (Cons V V)]
  [P? ((λ (x) e) ρ O) p?]
  [Ans V ERR]
  
  ; environment
  [ρ ([x ↦ V] ...)]
  [O ([x ↦ o′] ...)]
  [Γ ([o′ ↦ φ ...] ...)]
  
  [o ∅ o′]
  [o′ (acc ... x)]
  [acc car cdr]
  [φ P? (¬ P?) (Cons φ φ) (φ → φ)])

;; translates source to target language
(define-metafunction scpcf
  compile : any #|e in scpcf-src|# -> e
  [(compile (λ (x) any)) (λ (x) (compile any))]
  [(compile (if any ...)) (if (compile any) ...)]
  [(compile (μ (x) any)) (μ (x) (compile any))]
  [(compile (mon any_c any)) (MON (compile-c any_c) (compile any))]
  [(compile (let [x any_x] any)) (let [x (compile any_x)] (compile any))]
  [(compile (any_f any_x ...)) ((compile any_f) (compile any_x) ...)]
  [(compile any) any])

(define-metafunction scpcf
  compile-c : any #|c in scpcf-src|# -> c
  [(compile-c (flat any)) (flat (compile any))]
  [(compile-c (any_cx ↦ (λ (x) any_cy)))
   ((compile-c any_cx) ↦ (λ (x) (compile-c any_cy)))]
  [(compile-c (or/c any_1 any_2))
   (or/c (compile-c any_1) (compile-c any_2))]
  [(compile-c (and/c any_1 any_2))
   (and/c (compile-c any_1) (compile-c any_2))]
  [(compile-c (cons/c any_1 any_2))
   (cons/c (compile-c any_1) (compile-c any_2))]
  [(compile-c (μ (x) any)) (μ (x) (compile-c any))]
  [(compile-c x) x])

;; breaks mon-expressions into simple tests
(define-metafunction scpcf
  MON : c e -> e
  ; special rules to reduce cluttering
  [(MON c x) (MON-1 c x)]
  [(MON c v) (MON-1 c v)]
  [(MON (flat p?) e)
   (let [x e] (if (p? x) (refine x p?) blame))
   (where x ,(variable-not-in (term (v e)) (term A)))]
  
  [(MON (flat e_p) e)
   (let [x_p e_p]
     (let [x e]
       (if (x_p x) (refine x x_p) blame)))
   (where (x_p x) ,(variables-not-in (term (e_p e)) (term (P? A))))]
  [(MON (c_x ↦ (λ (x) c_y)) e)
   (let [f (MON (flat proc?) e)]
     (λ (x) (MON c_y (f (MON-1 c_x x)))))
   (where f ,(variable-not-in (term ((c_x ↦ (λ (x) c_y)) e)) (term F)))]
  [(MON (or/c c_1 c_2) e)
   (let [x_p (FC c_1)]
     (let [x e]
       (if (x_p x) (refine x x_p) (MON-1 c_2 x))))
   (where (x_p x) ,(variables-not-in (term ((or/c c_1 c_2) e)) (term (P? A))))]
  [(MON (and/c c_1 c_2) e) (MON c_2 (MON c_1 e))]
  [(MON (cons/c c_1 c_2) e)
   (let [x (MON (flat cons?) e)]
     (cons (MON c_1 (car x)) (MON c_2 (cdr x))))
   (where x ,(variable-not-in (term ((cons/c c_1 c_2) e)) (term A)))]
  [(MON (μ (x) c) e)
   ((μ (x) (λ (z) (MON-1 c z))) e)
   (where z ,(variable-not-in (term ((μ (x) c) e)) (term A)))]
  [(MON x e) (x e)])

;; specialized version of MON with less cluttering from temp vars
(define-metafunction scpcf
  MON-1 : c e -> e
  [(MON-1 (flat p?) e) (if (p? e) (refine e p?) blame)]
  [(MON-1 (flat e_p) e) (if (e_p e) (refine e e_p) blame)]
  [(MON-1 (c_x ↦ (λ (x) c_y)) e)
   (if (proc? e) (λ (x) (MON c_y (e (MON-1 c_x x)))) blame)]
  [(MON-1 (or/c c_1 c_2) e)
   (let [x_p (FC c_1)]
     (if (x_p e) (refine e x_p) (MON-1 c_2 e)))
   (where x_p ,(variable-not-in (term ((or/c c_1 c_2) e)) (term P?)))]
  [(MON-1 (and/c c_1 c_2) e) (MON-1 c_2 (MON-1 c_1 e))]
  [(MON-1 (cons/c c_1 c_2) x)
   (if (cons? x) (cons (MON c_1 (car x)) (MON c_2 (cdr x))) blame)]
  [(MON-1 (cons/c c_1 c_2) e)
   (let [x (MON-1 (flat cons?) e)] (cons (MON c_1 (car x)) (MON c_2 (cdr x))))
   (where x ,(variable-not-in (term ((cons/c c_1 c_2) e)) (term A)))]
  [(MON-1 (μ (x) c) e)
   ((μ (x) (λ (z) (MON-1 c z))) e)
   (where z ,(variable-not-in (term ((μ (x) c) e)) (term A)))]
  [(MON-1 x e) (x e)])

(define-metafunction scpcf
  FC : c -> e
  [(FC (flat e)) e]
  [(FC (or/c c_1 c_2))
   (λ (x) (if ((FC c_1) x) #t ((FC c_2) x)))
   (where x ,(variable-not-in (term (c_1 c_2)) (term A)))]
  [(FC (and/c c_1 c_2))
   (λ (x) (if ((FC c_1) x) ((FC c_2) x) #f))
   (where x ,(variable-not-in (term (c_1 c_2)) (term A)))]
  [(FC (cons/c c_1 c_2))
   (λ (x) (if (cons? x) (if ((FC c_1) x) ((FC c_2) x) #f) #f))
   (where x ,(variable-not-in (term (c_1 c_2)) (term A)))]
  [(FC (μ (x) c)) (μ (x) (FC c))]
  [(FC x) x])

(define-judgment-form scpcf
  #:mode     (⇓ I I I I O   O O)
  #:contract (⇓ Γ ρ O e Ans Γ o)
  
  [----- "var"
         (⇓ Γ ρ O v (close v (Γ-flush Γ ρ) O) Γ ∅)]
  [----- "val"
         (⇓ Γ ρ O x (Γ-refine (! ρ x) Γ (! O x)) Γ (! O x))]
  
  [(⇓ Γ ρ O e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O e_x V_x Γ_2 o_x)
   (⇓a Γ_2 V_f ([V_x o_x]) Ans Γ_3 o_a)
   ----- "app1"
   (⇓ Γ ρ O (e_f e_x) Ans Γ_3 o_a)]
  [(⇓ Γ ρ O e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O e_x V_x Γ_2 o_x)
   (⇓ Γ_2 ρ O e_y V_y Γ_3 o_y)
   (⇓a Γ_3 V_f ([V_x o_x] [V_y o_y]) Ans Γ_4 o_a)
   ----- "app2"
   (⇓ Γ ρ O (e_f e_x e_y) Ans Γ_4 o_a)]
  [(⇓ Γ ρ O e_f ERR Γ_1 o_f)
   ----- "app-err1"
   (⇓ Γ ρ O (e_f e_x ...) ERR Γ_1 ∅)]
  [(⇓ Γ ρ O e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O e_x ERR Γ_2 o_x)
   ----- "app-err2"
   (⇓ Γ ρ O (e_f e_x e_y ...) ERR Γ_2 ∅)]
  [(⇓ Γ ρ O e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O e_x V_x Γ_2 o_x)
   (⇓ Γ_2 ρ O e_y ERR Γ_3 o_y)
   ----- "app-err3"
   (⇓ Γ ρ O (e_f e_x e_y) ERR Γ_3 ∅)]
  
  [(⇓ Γ ρ O e V Γ_1 o)
   (where (any ... (#f Γ_2 o_t) any_1 ...) (δ false? (V o) Γ_1))
   (⇓ Γ_2 ρ O e_1 Ans Γ_3 o_a)
   ----- "if-true"
   (⇓ Γ ρ O (if e e_1 e_2) Ans Γ_3 o_a)]
  [(⇓ Γ ρ O e V Γ_1 o)
   (where (any ... (#t Γ_2 o_t) any_1 ...) (δ false? (V o) Γ_1))
   (⇓ Γ_2 ρ O e_2 Ans Γ_3 o_a)
   ----- "if-false"
   (⇓ Γ ρ O (if e e_1 e_2) Ans Γ_3 o_a)]
  [(⇓ Γ ρ O e ERR Γ_1 o)
   ----- "if-err"
   (⇓ Γ ρ O (if e e_1 e_2) ERR Γ_1 ∅)]
  
  [(⇓ Γ ρ O e_p V_p Γ_1 o_p)
   (⇓ Γ_1 ρ O e V Γ_2 o)
   ----- "refine"
   (⇓ Γ ρ O (refine e e_p) (REFINE V V_p) (Γ:: Γ_2 V_p o) o)]
  
  [(⇓ Γ ρ O e_x V_x Γ_1 o_x)
   (⇓ (Γ-reset Γ_1 x) (:: ρ [x ↦ V_x]) (:: O [x ↦ (default-o o_x (dom ρ) [x])]) e
      Ans Γ_2 o_a)
   ----- "let"
   (⇓ Γ ρ O (let [x e_x] e) Ans (Γ-del Γ_2 x) (default-o o_a (dom Γ) ∅))]
  
  [(⇓ Γ ρ O (subst e x (μ (x) e)) Ans Γ_1 o)
   ----- "μ"
   (⇓ Γ ρ O (μ (x) e) Ans Γ_1 o)]
  
  [----- "blame"
         (⇓ Γ ρ O blame ERR Γ ∅)])

(define-judgment-form scpcf
  #:mode     (⇓a I I I           O   O O)
  #:contract (⇓a Γ V ([V o] ...) Ans Γ o)
  [(⇓
    (Γ-reset (Γ-mk (dom ρ) Γ) x)
    (:: ρ [x ↦ V_x])
    (:: O [x ↦ (default-o o_x (del (dom ρ) x) [x])])
    e
    Ans Γ_1 o)
   ----- "app-λ"
   (⇓a Γ ((λ (x) e) ρ O) ([V_x o_x])
       Ans (Γ-upd Γ (Γ-del Γ_1 x)) (default-o o (del (dom Γ) x) ∅))]
  [(where (any ... (Ans Γ_1 o_a) any_1 ...) (δ o1 (V_x o_x) Γ))
   ----- "app-o1"
   (⇓a Γ o1 ([V_x o_x]) Ans Γ_1 o_a)]
  [(where (any ... (Ans Γ_1 o_a) any_1 ...) (δ o2 (V_x o_x) (V_y o_y) Γ))
   ----- "app-o2"
   (⇓a Γ o2 ([V_x o_x] [V_y o_y]) Ans Γ_1 o_a)])

(define-metafunction scpcf
  close : v ρ O -> V
  [(close (λ (x) e) ρ O) ((λ (x) e) ρ O)]
  [(close • ρ O) (•)]
  [(close b ρ O) b])

(define-metafunction scpcf
  REFINE : V φ -> V
  [(REFINE (• φ ...) φ_1) (• φ_1 φ ...)]
  [(REFINE V φ) V])

(define-metafunction scpcf
  subst : e x any -> e
  [(subst (λ (x) e) x any) (λ (x) e)]
  [(subst (λ (x) e) z any) (λ (x) (subst e z any))]
  [(subst x x any) any]
  [(subst x z any) x]
  [(subst (if e ...) x any) (if (subst e x any) ...)]
  [(subst (μ (x) e) x any) (μ (x) e)]
  [(subst (μ (x) e) z any) (μ (x) (subst e z any))]
  [(subst (let [x e_x] e) x any) (let [x (subst e_x x any)] e)]
  [(subst (let [x e_x] e) z any) (let [x (subst e_x z any)] (subst e z any))]
  [(subst (refine e ...) x any) (refine (subst e x any) ...)]
  [(subst (e ...) x any) ((subst e x any) ...)]
  [(subst a x any) a])

(define-metafunction scpcf
  Γ-flush : Γ ρ -> ρ
  [(Γ-flush () ρ) ρ]
  [(Γ-flush ([(acc ... x) ↦ φ ...] any ...) (any_1 ... [x ↦ (• φ_1 ...)] any_2 ...))
   (Γ-flush (any ...)
            (any_1 ... [x ↦ (• (mk-φ (acc ...) φ) ... φ_1 ...)] any_2 ...))]
  [(Γ-flush (any any_1 ...) ρ) (Γ-flush (any_1 ...) ρ)])

(define-metafunction scpcf
  Γ-refine : V Γ o′ -> V
  [(Γ-refine (• V ...) ([(acc ... acc_1 ... x) ↦ φ ...] any ...) (acc_1 ... x))
   (Γ-refine (• (mk-φ (acc ...) φ) ... V ...) (any ...) (acc_1 ... x))]
  [(Γ-refine (• V ...) (any_1 any ...) o) (Γ-refine (• V ...) (any ...) o)]
  [(Γ-refine V Γ o) V])



(define-metafunction scpcf
  mk-φ : (acc ...) φ -> φ
  [(mk-φ () φ) φ]
  [(mk-φ (car acc ...) φ) (mk-φ (acc ...) (Cons φ tt))]
  [(mk-φ (cdr acc ...) φ) (mk-φ (acc ...) (Cons tt φ))])

(define-metafunction scpcf
  Γ-del : Γ x ... -> Γ
  [(Γ-del (any ... [(acc ... x) ↦ φ ...] any_1 ...) x_1 ... x x_i ...)
   (Γ-del (any ... any_1 ...) x_1 ... x x_i ...)]
  [(Γ-del any x ...) any])

[define-metafunction scpcf
  Γ-mk : {x ...} Γ -> Γ
  [(Γ-mk {x ...} Γ) (Γ-upd ([(x) ↦ tt] ...) Γ)]]

(define-metafunction scpcf
  Γ-reset : Γ x -> Γ
  [(Γ-reset Γ x) ,(cons (term [(x) ↦ tt]) (term (Γ-del Γ x)))])

(define-metafunction scpcf
  Γ-upd : Γ Γ -> Γ
  [(Γ-upd Γ []) Γ]
  [(Γ-upd (any_1 ... [o ↦ φ ...] any_2 ...) ([o ↦ φ_1 ...] any_3 ...))
   (Γ-upd (any_1 ... [o ↦ φ_1 ...] any_2 ...) (any_3 ...))]
  [(Γ-upd (any_1 ... [(acc ... x) ↦ φ ...] any_2 ...)
          ([(acc_1 ... x) ↦ φ_1 ...] any_3 ...))
   (Γ-upd ([(acc_1 ... x) ↦ φ_1 ...] any_1 ... [(acc ... x) ↦ φ ...] any_2 ...)
          (any_3 ...))]
  [(Γ-upd Γ (any_1 any_2 ...)) (Γ-upd Γ (any_2 ...))])

(define-metafunction scpcf
  dom : any -> {x ...}
  [(dom ([x ↦ any] ...)) (x ...)]
  [(dom ([(acc ... x) ↦ any ...] ...)) (remove-duplicates (x ...))])

(define-metafunction scpcf
  remove-duplicates : {any ...} -> {any ...}
  [(remove-duplicates (x_1 ... x x_i ... x x_k ...))
   (remove-duplicates (x_1 ... x x_i ... x_k ...))]
  [(remove-duplicates any) any])

;; interprets primitive ops
(define-metafunction scpcf
  δ : op (V o) ... Γ -> {(Ans Γ o) ...}
  
  ; add1
  [(δ add1 (n o) Γ) {(,(add1 (term n)) Γ ∅)}]
  [(δ add1 ((• φ ...) o) Γ)
   ,(match (term (⊢? (φ ...) Γ o int?))
      ['Proved (term {((• int?) Γ ∅)})]
      ['Refuted (term {(ERR Γ ∅)})]
      ['Neither (term {((• int?) (Γ:: Γ int? o) ∅)
                       (ERR (Γ:: Γ (¬ int?) o) ∅)})])]
  [(δ add1 (V o) Γ) {(ERR Γ ∅)}]
  
  ; car, cdr
  [(δ car (V o) Γ)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V1 (Γ:: Γ cons? o) (acc-o car o)))]
       [`() (term (ERR (Γ:: Γ (¬ cons?) o) ∅))])
     (term (split-cons (V o) Γ)))]
  [(δ cdr (V o) Γ)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V2 (Γ:: Γ cons? o) (acc-o cdr o)))]
       [`() (term (ERR (Γ:: Γ (¬ cons?) o) ∅))])
     (term (split-cons (V o) Γ)))]
  
  ; +
  [(δ + (m o_m) (n o_n) Γ) {(,(+ (term m) (term n)) Γ ∅)}]
  [(δ + ((• φ ...) o_m) (n o_n) Γ) (δ + ((• φ ...) o_m) ((• int?) o_n) Γ)]
  [(δ + (m o_m) ((• φ ...) o_n) Γ) (δ + ((• int?) o_m) ((• φ ...) o_n) Γ)]
  [(δ + ((• φ_m ...) o_m) ((• φ_n ...) o_n) Γ)
   ,(match (term ((⊢? (φ_m ...) Γ o_m int?) (⊢? (φ_n ...) Γ o_n int?)))
      [`(Proved Proved) (term {((• int?) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {(ERR Γ ∅)})]
      [_ (term {((• int?) (Γ:: (Γ:: Γ int? o_m) int? o_n) ∅)
                (ERR Γ ∅)})])]
  
  ; cons
  [(δ cons (V_1 o_1) (V_2 o_2) Γ) {((Cons V_1 V_2) Γ ∅)}]
  
  ; predicates
  [(δ tt (V o) Γ) {(#t Γ ∅)}]
  [(δ p? ((• φ ...) o) Γ)
   ,(match (term (⊢? (φ ...) Γ o p?))
      ['Proved (term {(#t Γ ∅)})]
      ['Refuted (term {(#f Γ ∅)})]
      ['Neither (term {(#t (Γ:: Γ p? o) ∅)
                       (#f (Γ:: Γ (¬ p?) o) ∅)})])]
  [(δ p? (V o) Γ)
   ,(match (term (concrete-check p? V))
      [#t (term {(#t Γ ∅)})]
      [#f (term {(#f Γ ∅)})])]
  
  [(δ op (V o) ... Γ) {(ERR Γ ∅)}])

(define-metafunction scpcf
  concrete-check : p? V -> #t or #f
  [(concrete-check int? n) #t]
  [(concrete-check false? #f) #t]
  [(concrete-check proc? ((λ (x) e) ρ O)) #t]
  [(concrete-check proc? op) #t]
  [(concrete-check cons? (Cons V_1 V_2)) #t]
  [(concrete-check p? V) #f])

(define-metafunction scpcf
  ⊢? : (φ ...) Γ o p? -> Verified?
  [(⊢? (φ ...) Γ o tt) Proved]
  [(⊢? (any ... p?_1 any_1 ...) Γ o p?)
   Proved
   (where Proved (p-implies? p?_1 p?))]
  [(⊢? (any ... p?_1 any_1 ...) Γ o p?)
   Refuted
   (where Refuted (p-implies? p?_1 p?))]
  [(⊢? (any ... (¬ p?_1) any_1 ...) Γ o p?)
   Refuted
   (where Proved (p-implies? p? p?_1))]
  [(⊢? (any ... (Cons φ_1 φ_2) any_1 ...) p?)
   Proved
   (where Proved (p-implies? cons? p?))]
  [(⊢? (any ... (φ_1 → φ_2) any_1 ...) proc?)
   Proved
   (where Proved (p-implies? proc? p?))]
  [(⊢? (φ ...) Γ o p?) Neither])

(define-metafunction scpcf
  p-implies? : p? p? -> Verified?
  [(p-implies? p? p?) Proved]
  [(p-implies? p? tt) Proved]
  [(p-implies? p? p?_1) Refuted]) ; for now

;; split pair closure into 2, or () indicating not a pair
(define-metafunction scpcf
  split-cons : (V o) Γ -> {(V ...) ...} ; (V ...) being (V V) or ()
  [(split-cons ((Cons V_1 V_2) o) Γ) {(V_1 V_2)}]
  [(split-cons ((• φ ...) o) Γ)
   ,(match (term (acc-cons (φ ...) Neither))
      ['Neither (match (term (Γ⊢? Γ o cons?))
                  ['Proved (term {(Cons (•) (•))})]
                  ['Refuted (term {()})]
                  ['Neither (term { (Cons (•) (•))
                                    () })])]
      ['Refuted (term {()})]
      [`(,φs1 ,φs2) (term {((• ,@ φs1) (• ,@ φs2))})])]
  [(split-cons (V o) Γ) {()}])
(define-metafunction scpcf
  acc-cons : (φ ...) any -> {(φ ...) (φ ...)} or Refuted
  [(acc-cons any Refuted) Refuted]
  [(acc-cons ((¬ p?) φ ...) any)
   Refuted
   (where Proved (p-implies? cons? p?))]
  [(acc-cons (p? φ ...) any)
   Refuted
   (where Refuted (p-implies? p? cons?))]
  [(acc-cons (p? φ ...) Neither)
   (acc-cons (φ ...) ([][]))
   (where Proved (p-implies? p? cons?))]
  [(acc-cons (p? φ ...) ([φ_1 ...] [φ_2 ...]))
   (acc-cons (φ ...) ([φ_1 ...] [φ_2 ...]))
   (where Proved (p-implies? p? cons?))]
  [(acc-cons ((Cons φ_1 φ_2) φ ...) ([φ_l ...] [φ_r ...]))
   (acc-cons (φ ...) ([φ_1 φ_l ...] [φ_2 φ_r ...]))]
  [(acc-cons ((Cons φ_1 φ_2) φ ...) Neither)
   (acc-cons (φ ...) ([φ_1] [φ_2]))]
  [(acc-cons ((φ_x → φ_y) φ ...) any) Refuted]
  [(acc-cons (φ φ_1 ...) any) (acc-cons (φ_1 ...) any)]
  [(acc-cons () any) any])

(define-metafunction scpcf
  ! : ([any ↦ any] ...) any -> any
  [(! (any_1 ... [any_k ↦ any_v] any_n ...) any_k) any_v])
(define-metafunction scpcf
  :: : ([any ↦ any] ...) [any ↦ any] -> ([any ↦ any] ...)
  [(:: (any_1 ... [any_k ↦ any_v] any_n ...) [any_k ↦ any_u])
   (any_1 ... [any_k ↦ any_u] any_n ...)]
  [(:: (any ...) [any_k ↦ any_v]) ([any_k ↦ any_v] any ...)])
(define-metafunction scpcf
  Γ:: : Γ φ o -> Γ
  [(Γ:: Γ φ ∅) Γ]
  [(Γ:: (any ... [o ↦ tt] any_1 ...) φ o) (any ... [o ↦ φ] any_1 ...)]
  [(Γ:: (any ... [o ↦ φ_1 ... φ φ_k ...] any_1 ...) φ o)
   (any ... [o ↦ φ_1 ... φ φ_k ...] any_1 ...)]
  [(Γ:: (any ... [o ↦ φ_1 ...] any_1 ...) φ o)
   (any ... [o ↦ φ φ_1 ...] any_1 ...)]
  [(Γ:: (any ... [(acc ... x) ↦ φ_1 ...] any_1 ...) φ (acc_1 ... x))
   ([(acc_1 ... x) ↦ φ] any ... [(acc ... x) ↦ φ_1 ...] any_1 ...)])

(define-metafunction scpcf
  default-o : o {x ...} o -> o
  [(default-o (acc ... x) {z ... x y ...} o) (acc ... x)]
  [(default-o o any o_1) o_1])

(define-metafunction scpcf
  acc-o : acc o -> o
  [(acc-o any ∅) ∅]
  [(acc-o acc (acc_1 ... x)) (acc acc_1 ... x)])

(define (s-map f xs)
  (term (remove-duplicates ,(map f xs))))

(define-metafunction scpcf
  del : {any ...} any -> {any ...}
  [(del {any_1 ... any any_k ...} any) (del {any_1 ... any_k ...} any)]
  [(del any any_1) any])

(define-metafunction scpcf
  ev : any -> (Ans ...)
  [(ev e)
   (Ans ...)
   (where (Ans ...) ,(judgment-holds (⇓ [] [] [] e Ans Γ o) Ans))]
  [(ev any)
   (Ans ...)
   (where (Ans ...) ,(judgment-holds (⇓ [] [] [] (compile any) Ans Γ o) Ans))])

(map
 (λ (t)
   (term (,t compiles-to: (compile ,t) evaluates-to: (ev ,t))))
 (term {((mon ((flat int?) ↦ (λ (x) (flat int?))) (λ (x) (add1 x))) 4)
        (mon (μ (list?) (or/c (flat false?) (cons/c (flat tt) list?)))
             (cons 1 #f))}))