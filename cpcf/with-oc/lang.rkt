#lang racket
(require
 redex
 (only-in "lang-simple.rkt"
          cpcf
          :: !
          [subst subst1]
          [subst/c subst/c1]))
(provide
 scpcf
 ⇓ ⇓c APP MON
 dom Γ-refine Γ-upd Γ-mk Γ-del Γ-reset default-o)
         

(define-extended-language scpcf cpcf
  [e ....
     (let [x e] e)
     (let ([x e] [x e] ...) e)
     (or e e ...)
     (and e e ...)
     (begin e e ...)
     (cond [e e] ... [else e])]
  [v .... •]
  
  ; proposition environment
  [Γ ([o′ ↦ φ ...] ...)]
  [o ∅ o′]
  [o′ (acc ... x)]
  [φ p? (¬ p?)]
  
  ; path environment
  [O ([x ↦ o′] ...)]
  
  ; closed value
  [V b
     ((λ x e) ρ O)
     (Arr (c ↦ (λ x c) ρ) V)
     (Cons V V)
     (• D ...)]
  [EA function n #t #f (Cons EA EA) (• D ...) blame]
      
  
  ; evaluated contract
  [D (Flat V)
     (c ↦ (λ x c) ρ O)
     (Or/c c c ρ O)
     (And/c D D)
     (Cons/c D D)]
  )

;; evaluation
(define-judgment-form scpcf
  #:mode     (⇓ I I I I O O O)
  #:contract (⇓ Γ ρ O e A Γ o)
  [----- "blame"
   (⇓ Γ ρ O blame blame Γ ∅)]
  [----- "val"
   (⇓ Γ ρ O v [close v Γ ρ O] Γ ∅)]
  [----- "var"
   (⇓ Γ ρ O x [Γ-refine (! ρ x) Γ (! O x)] Γ [! O x])]
  
  [(⇓ Γ ρ O e V_t Γ_1 o_t)
   (where (any ... (#f Γ_2 o_t′) any_1 ...) (δ false? (V_t o_t) Γ_1))
   (⇓ Γ_2 ρ O e_1 A Γ_3 o_a)
   ----- "if-true"
   (⇓ Γ ρ O (if e e_1 e_2) A Γ_3 o_a)]
  [(⇓ Γ ρ O e V_t Γ_1 o_t)
   (where (any ... (#t Γ_2 o_t′) any_1 ...) (δ false? (V_t o_t) Γ_1))
   (⇓ Γ_2 ρ O e_2 A Γ_3 o_a)
   ----- "if-false"
   (⇓ Γ ρ O (if e e_1 e_2) A Γ_3 o_a)]
  [(⇓ Γ ρ O e blame Γ_1 o)
   ----- "if-err"
   (⇓ Γ ρ O (if e e_1 e_2) blame Γ_1 ∅)]
  
  [(⇓ Γ ρ O e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O e_x V_x Γ_2 o_x)
   (APP Γ_2 V_f ([V_x o_x]) A Γ_3 o_a)
   ----- "app-1"
   (⇓ Γ ρ O (e_f e_x) A Γ_3 o_a)]
  [(⇓ Γ ρ O e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O e_x V_x Γ_2 o_x)
   (⇓ Γ_2 ρ O e_y V_y Γ_3 o_y)
   (APP Γ_3 V_f ([V_x o_x] [V_y o_y]) A Γ_4 o_a)
   ----- "app-2"
   (⇓ Γ ρ O (e_f e_x e_y) A Γ_4 o_a)]
  [(⇓ Γ ρ O e_f blame Γ_1 o)
   ----- "app-err-1"
   (⇓ Γ ρ O (e_f e_x ...) blame Γ_1 ∅)]
  [(⇓ Γ ρ O e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O e_x blame Γ_2 o_x)
   ----- "app-err-2"
   (⇓ Γ ρ O (e_f e_x e_y ...) blame Γ_2 ∅)]
  [(⇓ Γ ρ O e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O e_x V_x Γ_2 o_x)
   (⇓ Γ_2 ρ O e_y blame Γ_3 o_y)
   ----- "app-err-3"
   (⇓ Γ ρ O (e_f e_x e_y) blame Γ_3 ∅)]
  
  [(⇓ Γ ρ O [subst e x (μ x e)] A Γ_1 o_a)
   ----- "μ"
   (⇓ Γ ρ O (μ x e) A Γ_1 o_a)]
  
  [(⇓c Γ ρ O c D Γ_1)
   (⇓ Γ_1 ρ O e V Γ_2 o)
   (MON Γ_2 D (V o) A Γ_3)
   ----- "mon"
   (⇓ Γ ρ O (mon c e) A Γ_3 o)]
  [(⇓c Γ ρ O c blame Γ_1)
   ----- "mon-err-c"
   (⇓ Γ ρ O (mon c e) blame Γ_1 ∅)]
  [(⇓c Γ ρ O c D Γ_1)
   (⇓ Γ_1 ρ O e blame Γ_2 o)
   ----- "mon-err-e"
   (⇓ Γ ρ O (mon c e) blame Γ_2 ∅)])

;; contract evaluation
(define-judgment-form scpcf
  #:mode     (⇓c I I I I O   O)
  #:contract (⇓c Γ ρ O c Dns Γ)
  [(⇓ Γ ρ O e V Γ_1 o)
   ----- "flat"
   (⇓c Γ ρ O (flat e) (Flat V) Γ_1)]
  [(⇓ Γ ρ O e blame Γ_1 o)
   ----- "flat-err"
   (⇓c Γ ρ O (flat e) blame Γ_1)]
  
  [----- "func/c"
   (⇓c Γ ρ O (c_x ↦ (λ x c_y)) (c_x ↦ (λ x c_y) ρ O) Γ)]
   
  [(⇓c Γ ρ O c_1 D_1 Γ_1)
   (⇓c Γ_1 ρ O c_2 D_2 Γ_2)
   ----- "and/c"
   (⇓c Γ ρ O (and/c c_1 c_2) (And/c D_1 D_2) Γ_2)]
  [(⇓c Γ ρ O c_1 blame Γ_1)
   ----- "and/c-err-1"
   (⇓c Γ ρ O (and/c c_1 c_2) blame Γ_1)]
  [(⇓c Γ ρ O c_1 D_1 Γ_1)
   (⇓c Γ_1 ρ O c_2 blame Γ_2)
   ----- "and/c-err-2"
   (⇓c Γ ρ O (and/c c_1 c_2) blame Γ_2)]
  
  [----- "or/c"
   (⇓c Γ ρ O (or/c c_1 c_2) (Or/c c_1 c_2 ρ O) Γ)]
  
  [(⇓c Γ ρ O c_1 D_1 Γ_1)
   (⇓c Γ_1 ρ O c_2 D_2 Γ_2)
   ----- "cons/c"
   (⇓c Γ ρ O (cons/c c_1 c_2) (Cons/c D_1 D_2) Γ_2)]
  [(⇓c Γ ρ O c_1 blame Γ_1)
   ----- "cons/c-err-1"
   (⇓c Γ ρ O (cons/c c_1 c_2) blame Γ_1)]
  [(⇓c Γ ρ O c_1 D_1 Γ_1)
   (⇓c Γ_1 ρ O c_2 D_2 Γ_2)
   ----- "cons/c-err-2"
   (⇓c Γ ρ O (cons/c c_1 c_2) blame Γ_2)]
  
  [(⇓c Γ ρ O [subst/c c x (μ x c)] Dns Γ_1)
   ----- "μ/c"
   (⇓c Γ ρ O (μ x c) Dns Γ_1)])

;; application
(define-judgment-form scpcf
  #:mode     (APP I I I           O O O)
  #:contract (APP Γ V ([V o] ...) A Γ o)
  
  [(⇓ [Γ-reset (Γ-mk (dom ρ) Γ) x]
      [:: ρ (x ↦ V)]
      [:: O (x ↦ (default-o o (dom ρ) [x]))]
      e
      A Γ_1 o_a)
   ----- "app-λ"
   (APP Γ ((λ x e) ρ O) ([V o]) A (Γ-upd Γ (Γ-del Γ x)) (default-o o_a (dom Γ) ∅))]
  
  [(⇓c [Γ-mk (dom ρ) Γ] ρ O c_x D_x Γ_1)
   (where o_v (default-o o (dom Γ_1) ∅))
   (MON Γ_1 D_x (V o_v) V_1 Γ_2)
   (⇓c [Γ-reset Γ_2 x] [:: ρ [x ↦ V_1]] [:: O [x ↦ o_v]] c_y D_y Γ_3)
   (APP Γ_3 V_f (V_1 o_v) V_y Γ_4 o_y)
   (MON Γ_4 D_y (V_y o_y) A Γ_5)
   ----- "app-arr"
   (APP Γ (Arr (c_x ↦ (λ x c_y) ρ O) V_f) ([V o])
        A (Γ-upd Γ (Γ-del Γ_5 x)) (default-o o_y (dom Γ) ∅))]
  
  [(where (any ... (A Γ_1 o_a) any_1 ...) (δ op (V o) ... Γ))
   ----- "app-prim"
   (APP Γ op ([V o] ...) A Γ_1 o_a)])

;; monitoring
(define-judgment-form scpcf
  #:mode     (MON I I I     O O)
  #:contract (MON Γ D (V o) A Γ)
  [(APP Γ V_p ([V o]) V_t Γ_1 o_t)
   (where (any ... (#f Γ_2 o_t′) any_1 ...) (δ false? (V_t o_t) Γ_1))
   ----- "flat"
   (MON Γ (Flat V_p) (V o) (refine V (Flat V_p)) Γ_2)]
  [(APP Γ V_p ([V o]) V_t Γ_1 o_t)
   (where (any ... (#t Γ_2 o_t′) any_1 ...) (δ false? (V_t o_t) Γ_1))
   ----- "flat-fail"
   (MON Γ (Flat V_p) (V o) blame Γ_2)]
  [(APP Γ V_p ([V o]) blame Γ_1 o)
   ----- "flat-err"
   (MON Γ (Flat V_p) (V o) blame Γ_1)]
  
  [(where (any ... (#f Γ_1 o) any_1 ...) (δ proc? (V o) Γ))
   ----- "func/c-fail"
   (MON Γ (c_x ↦ (λ x c_y) ρ O) (V o) blame Γ_1)]
  [(where (any ... (#t Γ_1 o) any_1 ...) (δ proc? (V o) Γ))
   ----- "func/c"
   (MON Γ (c_x ↦ (λ x c_y) ρ O) (V o) (Arr (c_x ↦ (λ x c_y) ρ O) V) Γ_1)]
  
  [(⇓ (Γ-mk (dom ρ) Γ) ρ O (FC c_1) V_p Γ_1 o_p)
   (APP (Γ-upd Γ Γ_1) V_p (V o) V_t Γ_2 o_t)
   (where (any ... (#f Γ_3 o_t′) any_1 ...) (δ false? (V_t o_t) Γ_2))
   ----- "or/c-1"
   (MON Γ (Or/c c_1 c_2 ρ O) (V o) (refine V (Flat V_p)) Γ_3)]
  [(⇓ (Γ-mk (dom ρ) Γ) ρ O (FC c_1) V_p Γ_1 o_p)
   (APP (Γ-upd Γ Γ_1) V_p (V o) V_t Γ_2 o_t)
   (where (any ... (#t Γ_3 o_t′) any_1 ...) (δ false? (V_t o_t) Γ_2))
   (⇓c (Γ-mk (dom ρ) Γ_3) ρ O c_2 D_2 Γ_4)
   (MON (Γ-upd Γ_3 Γ_4) D_2 (V o) A Γ_5)
   ----- "or/c-2"
   (MON Γ (Or/c c_1 c_2 ρ O) (V o) A Γ_5)]
  
  [(MON Γ D_1 (V o) V_1 Γ_1)
   (MON Γ_1 D_2 (V_1 o) A Γ_2)
   ----- "and/c"
   (MON Γ (And/c D_1 D_2) (V o) A Γ_2)]
  [(MON Γ D_1 (V o) blame Γ_1)
   ----- "and/c-fail"
   (MON Γ (And/c D_1 D_2) (V o) blame Γ_1)]
  
  [(where (any ... (V_1 Γ_1 o_1) any_1 ...) (δ car (V o) Γ))
   (where (any ... (V_2 Γ_2 o_1) any_1 ...) (δ cdr (V o) Γ))
   (MON Γ_2 D_1 V_1 V_1′ Γ_3)
   (MON Γ_3 D_2 V_2 V_2′ Γ_4)
   ----- "cons/c"
   (MON Γ (Cons/c D_1 D_2) (V o) (Cons V_1′ V_2′) Γ_4)]
  [(where (any ... (blame Γ_1 o_1) any_1 ...) (δ car (V o) Γ))
   ----- "cons/c-err-1"
   (MON Γ (Cons/c D_1 D_2) (V o) blame Γ_1)]
  [(where (any ... (V_1 Γ_1 o_1) any_1 ...) (δ car (V o) Γ))
   (where (any ... (V_2 Γ_2 o_1) any_1 ...) (δ cdr (V o) Γ))
   (MON Γ_2 D_1 V_1 blame Γ_3)
   ----- "cons/c-err-2"
   (MON Γ (Cons/c D_1 D_2) (V o) blame Γ_3)]
  [(where (any ... (V_1 Γ_1 o_1) any_1 ...) (δ car (V o) Γ))
   (where (any ... (V_2 Γ_2 o_1) any_1 ...) (δ cdr (V o) Γ))
   (MON Γ_2 D_1 V_1 V_1′ Γ_3)
   (MON Γ_3 D_2 V_2 blame Γ_4)
   ----- "cons/c-err-3"
   (MON Γ (Cons/c D_1 D_2) (V o) blame Γ_4)]
  )

(define-metafunction scpcf
  acc-o : acc o -> o
  [(acc-o acc (acc_1 ... x)) (acc acc_1 ... x)]
  [(acc-o acc o) ∅])
(define-metafunction scpcf
  dom : any -> {x ...}
  [(dom ([x ↦ any] ...)) {x ...}]
  [(dom ([(acc ... x) ↦ any ...] ...)) (remove-dups {x ...})])
(define-metafunction scpcf
  remove-dups : {any ...} -> {any ...}
  [(remove-dups {any_1 ... any any_2 ... any any_3 ...})
   (remove-dups {any_1 ... any any_2 ... any_3 ...})]
  [(remove-dups any) any])

(define-metafunction scpcf
  close : v Γ ρ O -> V
  [(close b Γ ρ O) b]
  [(close • Γ ρ O) (•)]
  [(close (λ x e) Γ ρ O) ((λ x e) (Γ-flush Γ ρ) O)])

;; 'flushes' all propositions in Γ into ρ as refinining contracts for •'s
(define-metafunction scpcf
  Γ-flush : Γ ρ -> ρ
  [(Γ-flush [] ρ) ρ]
  [(Γ-flush ([(acc ... x) ↦ φ_1 φ ...] any ...)
            (any_1 ... [x ↦ V] any_2 ...))
   (Γ-flush ([(acc ... x) ↦ φ ...] any ...)
            (any_1 ... [x ↦ (refine V (mk-D (acc ...) φ_1))] any_2 ...))]
  [(Γ-flush (any_1 any ...) ρ) (Γ-flush (any ...) ρ)])

(define-metafunction scpcf
  Γ: : Γ [o ↦ φ] -> Γ
  [(Γ: Γ [∅ ↦ φ]) Γ]
  [(Γ: (any ... [o′ ↦ φ_1 ... φ φ_i ...] any_1 ...) [o′ ↦ φ])
   (any ... [o′ ↦ φ_1 ... φ φ_i ...] any_1 ...)]
  [(Γ: (any ... [o′ ↦ φ_1 ...] any_1 ...) [o′ ↦ φ])
   (any ... [o′ ↦ φ φ_1 ...] any_1 ...)]
  [(Γ: (any ... [(acc ... x) ↦ φ ...] any_1 ...) [(acc_1 ... x) ↦ φ_1])
   ([(acc_1 ... x) ↦ φ_1] any ... [(acc ... x) ↦ φ ...] any_1 ...)])

(define-metafunction scpcf
  Γ-del : Γ x -> Γ
  [(Γ-del (any ... [(acc ... x) ↦ φ ...] any_1 ...) x)
   (Γ-del (any ... any_1 ...) x)]
  [(Γ-del Γ x) Γ])

(define-metafunction scpcf
  Γ-mk : {x ...} Γ -> Γ
  [(Γ-mk {x ...} Γ) (Γ-upd ([(x) ↦] ...) Γ)])
(define-metafunction scpcf
  Γ-upd : Γ Γ -> Γ
  [(Γ-upd Γ ()) Γ]
  [(Γ-upd (any_1 ... [(acc ... x) ↦ φ ...] any_2 ...)
          ([(acc ... x) ↦ φ_1 ...] any ...))
   (Γ-upd (any_1 ... [(acc ... x) ↦ φ ... φ_1 ...] any_2 ...) (any ...))]
  [(Γ-upd (any_1 ... [(acc ... x) ↦ φ ...] any_2 ...)
          ([(acc_1 ... x) ↦ φ_1 ...] any ...))
   (Γ-upd ([(acc_1 ... x) ↦ φ_1 ...] any_1 ... [(acc ... x) ↦ φ ...] any_2 ...)
          (any ...))]
  [(Γ-upd Γ (any_1 any ...)) (Γ-upd Γ (any ...))])

(define-metafunction scpcf
  Γ-reset : Γ x -> Γ
  [(Γ-reset Γ x) ([(x) ↦] any ...) (where (any ...) (Γ-del Γ x))])

(define tt (term (λ x #t)))
(define TT (term (Flat (,tt () ()))))
(define-metafunction scpcf
  mk-D : (acc ...) φ -> D
  [(mk-D any (¬ p?)) (mk-D′ any ,TT)] ; lose something for now
  [(mk-D any p?) (mk-D′ any (Flat p?))])
(define-metafunction scpcf
  mk-D′ : (acc ...) D -> D
  [(mk-D′ () D) D]
  [(mk-D′ (car acc ...) D) (mk-D′ (acc ...) (Cons/c D ,TT))]
  [(mk-D′ (cdr acc ...) D) (mk-D′ (acc ...) (Cons/c ,TT D))])
   

;; interprets primitive ops
(define-metafunction scpcf
  δ : op (V o) ... Γ -> {(A Γ o) ...}
  
  ; add1
  [(δ add1 (n o) Γ) {(,(add1 (term n)) Γ ∅)}]
  [(δ add1 ((• D ...) o) Γ)
   ,(match (term (proved? (D ...) Γ o int?))
      ['Proved (term {((• (Flat int?)) Γ ∅)})]
      ['Refuted (term {(blame Γ ∅)})]
      ['Neither (term {((• (Flat int?)) (Γ: Γ [o ↦ int?]) ∅)
                       (blame Γ ∅)})])]
  [(δ add1 (V o) Γ) {(blame Γ ∅)}]
  
  ; car, cdr
  [(δ car ((Cons V_1 V_2) o) Γ) {(V_1 Γ (acc-o car o))}]
  [(δ car (V o) Γ)
   ,(s-map (match-lambda
             [`(#t ,Γ1 ,ot) (term ((•) ,Γ1 [acc-o car o]))]
             [`(#f ,Γ1 ,ot) (term (blame ,Γ1 ∅))])
           (term (δ cons? (V o) Γ)))]
  [(δ cdr ((Cons V_1 V_2) o) Γ) {(V_1 Γ (acc-o cdr o))}]
  [(δ cdr (V o) Γ)
   ,(s-map (match-lambda
             [`(#t ,Γ1 ,ot) (term ((•) ,Γ1 [acc-o cdr o]))]
             [`(#f ,Γ1 ,ot) (term (blame ,Γ1 ∅))])
           (term (δ cons? (V o) Γ)))]
  
  ; +
  [(δ + (m o_m) (n o_n) Γ) {(,(+ (term m) (term n)) Γ ∅)}]
  [(δ + ((• D ...) o_m) (n o_n) Γ) (δ + ((• D ...) o_m) ((• (Flat int?)) o_n) Γ)]
  [(δ + (m o_m) ((• D ...) o_n) Γ) (δ + ((• (Flat int?)) o_m) ((• D ...) o_n) Γ)]
  [(δ + ((• D_1 ...) o_m) ((• D_2 ...) o_n) Γ)
   ,(match (term ((proved? (D_1 ...) Γ o_m int?) (proved? (D_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {((• (Flat int?)) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {(blame Γ ∅)})]
      [_ (term {((• (Flat int?)) (Γ: (Γ: Γ [o_m ↦ int?]) [o_n ↦ int?]) ∅)
                (blame Γ ∅)})])]
  
  ; cons
  [(δ cons (V_1 o_1) (V_2 o_2) Γ) {((Cons V_1 V_2) Γ ∅)}]
  
  ; predicates
  [(δ p? ((• D ...) o) Γ)
   ,(match (term (proved? (D ...) Γ o p?))
      ['Proved (term {(#t Γ ∅)})]
      ['Refuted (term {(#f Γ ∅)})]
      ['Neither (term {(#t (Γ: Γ [o ↦ p?]) ∅) (#f (Γ: Γ [o ↦ (¬ p?)]) ∅)})])]
  [(δ p? (V o) Γ) {((concrete-check p? V) Γ ∅)}]
  
  [(δ op (V o) ... Γ) {(blame Γ ∅)}])

(define-metafunction scpcf
  proved? : (D ...) Γ o p? -> Proved or Refuted or Neither
  [(proved? (any ... (Flat p?) any_1 ...) Γ o p?) Proved]
  [(proved? (D ...) (any ... [o ↦ φ ... (¬ p?) φ_1 ...]) o p?) Refuted]
  [(proved? (any ... (Flat p?) any_1 ...) Γ o p?_1) Refuted] ; for now
  [(proved? (D ...) Γ o p?) Neither])

;; checks predicates on concrete values
(define-metafunction scpcf
  concrete-check : p? V -> #t or #f
  [(concrete-check int? n) #t]
  [(concrete-check false? #f) #t]
  [(concrete-check proc? ((λ x e) ρ O)) #t]
  [(concrete-check proc? (Arr D V)) #t]
  [(concrete-check proc? op) #t]
  [(concrete-check cons? (Cons V_1 V_2)) #t]
  [(concrete-check p? V) #f])

; just for now ...
(define-metafunction scpcf
  refine : V D -> V
  [(refine (• D ...) (Flat V)) (• (Flat V) D ...)]
  [(refine (•) (Cons/c c_1 c_2 ρ O))
   (Cons (refine (•) D_1) (refine (•) D_2))
   (where (D_1) ,(judgment-holds (⇓c (Γ-mk (dom ρ) ()) ρ O c_1 D Γ) D))
   (where (D_2) ,(judgment-holds (⇓c (Γ-mk (dom ρ) ()) ρ O c_2 D Γ) D))]
  [(refine (Cons V_1 V_2) (Cons/c c_1 c_2 ρ O))
   (Cons (refine V_1 D_1) (refine V_2 D_2))
   (where (D_1) ,(judgment-holds (⇓c (Γ-mk (dom ρ) ()) ρ O c_1 D Γ) D))
   (where (D_2) ,(judgment-holds (⇓c (Γ-mk (dom ρ) ()) ρ O c_2 D Γ) D))]
  [(refine V D) V])

(define-metafunction scpcf
  Γ-refine : V Γ o -> V
  [(Γ-refine V (any ... [(acc_1 ... acc ... x) ↦ φ φ_1 ...] any_1 ...) (acc ... x))
   (Γ-refine (refine V (mk-D (acc_1 ...) φ))
             (any ... [(acc_1 ... acc ... x) ↦ φ_1 ...] any_1 ...)
             (acc ... x))]
  [(Γ-refine V Γ o) V])

(define-metafunction/extension subst1 scpcf
  subst : e x any -> e
  [(subst • x any) •])
(define-metafunction/extension subst/c1 scpcf
  subst/c : c x any -> c)

(define-metafunction scpcf
  desug : e -> e
  [(desug (λ x e)) (λ x (desug e))]
  [(desug v) v]
  [(desug x) x]
  [(desug (e_0 e_1 e_2 ...)) ((desug e_0) (desug e_1) (desug e_2) ...)]
  [(desug (if e e_1 e_2)) (if (desug e) (desug e_1) (desug e_2))]
  [(desug (mon c e)) (mon (desug-c c) (desug e))]
  [(desug (μ x e)) (μ x (desug e))]
  [(desug (and e)) (desug e)]
  [(desug (and e_1 e_2 ...)) (if (desug e_1) (desug (and e_2 ...)) #f)]
  [(desug (or e)) (desug e)]
  [(desug (or e_1 e_2 ...))
   ((λ x_tmp (if x_tmp x_tmp (desug (or e_2 ...)))) (desug e_1))
   (where x_tmp ,(variable-not-in (term (e_1 e_2 ...)) (term tmp)))]
  [(desug (let [x e_x] e)) ((λ x (desug e)) (desug e_x))]
  [(desug (let ([x e_x]) e)) ((λ x (desug e)) (desug e_x))]
  [(desug (let ([x_1 e_1] [x_2 e_2] ...) e))
   ((λ x_1 (desug (let ([x_2 e_2] ...) e))) (desug e_1))]
  [(desug (cond [else e])) (desug e)]
  [(desug (cond [e_1 e_2] any ...))
   (if (desug e_1) (desug e_2) (desug (cond any ...)))]
  [(desug (begin e)) (desug e)]
  [(desug (begin e_1 e_2 ...))
   ((λ x_tmp (desug (begin e_2 ...))) (desug e_1))
   (where x_tmp ,(variable-not-in (term (e_1 e_2 ...)) (term tmp)))])
(define-metafunction scpcf
  desug-c : c -> c
  [(desug-c (flat e)) (flat (desug e))]
  [(desug-c (or/c c_1 c_2)) (or/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (and/c c_1 c_2)) (and/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (cons/c c_1 c_2)) (cons/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (c_x ↦ (λ x c_y))) ((desug-c c_x) ↦ (λ x (desug-c c_y)))]
  [(desug-c (μ x c)) (μ x (desug-c c))]
  [(desug-c x) x])

(define-metafunction scpcf
  ev : e -> {EA ...}
  [(ev e)
   ((A->EA A) ...)
   (where (A ...) ,(judgment-holds (⇓ () () () (desug e) A Γ o) A))])
(define-metafunction scpcf
  A->EA : A -> EA
  [(A->EA V) function (where ((#t Γ o)) (δ proc? (V ∅) ()))]
  [(A->EA (Cons V_1 V_2)) (Cons (A->EA V_1) (A->EA V_2))]
  [(A->EA A) A])

(define (s-map f xs)
  (set->list (list->set (map f xs))))
  
(define-metafunction scpcf
  default-o : o {x ...} o -> o
  [(default-o (acc ... x) {z ... x y ...} o) (acc ... x)]
  [(default-o o_1 {x ...} o_2) o_2])