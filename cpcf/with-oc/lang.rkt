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
 ⇓ ⇓c APP MON FC δ
 ρ-upd ρ+ ρ- ρ:
 refine proves? V-upd
 dom acc+ default-o)
         
(define-extended-language scpcf cpcf
  [v .... •]
  
  ; path environment
  [O ([x ↦ o′] ...)]
  [o ∅ o′]
  [o′ (acc ... x)]
  
  [φ p? (¬ p?)]
  
  ; closed value
  [V b
     ((λ x e) ρ O)
     (Arr (c ↦ (λ x c) ρ O) V)
     (Cons V V)
     (• C ...)]
  [EA function n #t #f (Cons EA EA) (• C ...) • blame]
      
  ; evaluated contract
  [C V
     (c ↦ (λ x c) ρ O)
     (Cons/c c c ρ O)
     (Or/c C C)
     (And/c C C)]
  [Proved? Proved Refuted Neither]
  
  ; convenient patterns
  [bool #t #f]
  [PROC ((λ x e) ρ O) (Arr (c ↦ (λ x c) ρ O) V) op]
  )

;; evaluation
(define-judgment-form scpcf
  #:mode     (⇓ I I I O O O)
  #:contract (⇓ ρ O e A ρ o)
  [----- "blame"
   (⇓ ρ O blame blame ρ ∅)]
  [----- "val"
   (⇓ ρ O v [close v ρ O] ρ ∅)]
  [----- "var"
   (⇓ ρ O x [! ρ x] ρ [! O x])]
  
  [(⇓ ρ O e V_t ρ_1 o_t)
   (δ ρ_1 false? ([V_t o_t]) #f ρ_2 o_t′)
   (⇓ ρ_2 O e_1 A ρ_3 o_a)
   ----- "if-true"
   (⇓ ρ O (if e e_1 e_2) A ρ_3 o_a)]
  [(⇓ ρ O e V_t ρ_1 o_t)
   (δ ρ_1 false? ([V_t o_t]) #t ρ_2 o_t′)
   (⇓ ρ_2 O e_2 A ρ_3 o_a)
   ----- "if-false"
   (⇓ ρ O (if e e_1 e_2) A ρ_3 o_a)]
  [(⇓ ρ O e blame ρ_1 o)
   ----- "if-err"
   (⇓ ρ O (if e e_1 e_2) blame ρ_1 ∅)]
  
  [(⇓ ρ O e_f V_f ρ_1 o_f)
   (⇓ ρ_1 O e_x V_x ρ_2 o_x)
   (APP ρ_2 V_f ([V_x o_x]) A ρ_3 o_a)
   ----- "app-1"
   (⇓ ρ O (e_f e_x) A ρ_3 o_a)]
  [(⇓ ρ O e_f V_f ρ_1 o_f)
   (⇓ ρ_1 O e_x V_x ρ_2 o_x)
   (⇓ ρ_2 O e_y V_y ρ_3 o_y)
   (APP ρ_3 V_f ([V_x o_x] [V_y o_y]) A ρ_4 o_a)
   ----- "app-2"
   (⇓ ρ O (e_f e_x e_y) A ρ_4 o_a)]
  [(⇓ ρ O e_f blame ρ_1 o)
   ----- "app-err-1"
   (⇓ ρ O (e_f e_x ...) blame ρ_1 ∅)]
  [(⇓ ρ O e_f V_f ρ_1 o_f)
   (⇓ ρ_1 O e_x blame ρ_2 o_x)
   ----- "app-err-2"
   (⇓ ρ O (e_f e_x e_y ...) blame ρ_2 ∅)]
  [(⇓ ρ O e_f V_f ρ_1 o_f)
   (⇓ ρ_1 O e_x V_x ρ_2 o_x)
   (⇓ ρ_2 O e_y blame ρ_3 o_y)
   ----- "app-err-3"
   (⇓ ρ O (e_f e_x e_y) blame ρ_3 ∅)]
  
  [(⇓c ρ O c C)
   (⇓ ρ O e V ρ_1 o)
   (MON ρ_1 C (V o) A ρ_2)
   ----- "mon"
   (⇓ ρ O (mon c e) A ρ_2 o)]
  [(⇓c ρ O c C)
   (⇓ ρ O e blame ρ_1 o)
   ----- "mon-err"
   (⇓ ρ O (mon c e) blame ρ_1 ∅)])

;; contract evaluation
(define-judgment-form scpcf
  #:mode     (⇓c I I I O)
  #:contract (⇓c ρ O c C)
  [----- "flat"
   (⇓c ρ O (flat v) [close v ρ O])]
  
  [----- "func/c"
   (⇓c ρ O (c_x ↦ (λ x c_y)) (c_x ↦ (λ x c_y) ρ O))]
   
  [(⇓c ρ O c C) ...
   ----- "and/c"
   (⇓c ρ O (and/c c ...) (And/c C ...))]
  
  [(⇓c ρ O c C) ...
   ----- "or/c"
   (⇓c ρ O (or/c c ...) (Or/c C ...))]
  
  [----- "cons/c"
   (⇓c ρ O (cons/c c_1 c_2) (Cons/c c_1 c_2 ρ O))]
  
  [(⇓c ρ O [subst/c c x (μ x c)] C)
   ----- "μ/c"
   (⇓c ρ O (μ x c) C)])

;; application
(define-judgment-form scpcf
  #:mode     (APP I I I           O O O)
  #:contract (APP ρ V ([V o] ...) A ρ o)
  
  [(⇓ [:: (ρ-upd ρ_f ρ) (x ↦ V)]
      [:: O_f (x ↦ (default-o o (dom ρ) [x]))]
      e
      A ρ_1 o_a)
   ----- "app-λ"
   (APP ρ ((λ x e) ρ_f O_f) ([V o]) A (ρ-upd ρ (ρ- ρ_1 x)) (default-o o_a (dom ρ) ∅))]
  
  [(⇓c (ρ-upd ρ_c ρ) O_c c_x C_x)
   (MON ρ C_x (V_x o_x) V_x′ ρ_1)
   (APP ρ_1 V_f ([V_x′ o_x]) V_y ρ_2 o_y)
   (⇓c [:: (ρ-upd ρ_c ρ_2) (x ↦ V_x′)]
       [:: O_c (x ↦ (default-o o_x (dom ρ_c) [x]))]
       c_y C_y)
   (MON ρ_2 C_y (V_y o_y) A ρ_3)
   ----- "app-arr"
   (APP ρ (Arr (c_x ↦ (λ x c_y) ρ_c O_c) V_f) ([V_x o_x]) A ρ_3 o_y)]
  [(⇓c (ρ-upd ρ_c ρ) O_c c_x C_x)
   (MON ρ C_x (V_x o_x) blame ρ_1)
   ----- "arr-err-1"
   (APP ρ (Arr (c_x ↦ (λ x c_y) ρ_c O_c) V_f) ([V_x o_x]) blame ρ_1 ∅)]
  [(⇓c (ρ-upd ρ_c ρ) O_c c_x C_x)
   (MON ρ C_x (V_x o_x) V_x′ ρ_1)
   (APP ρ_1 V_f ([V_x′ o_x]) blame ρ_2 o_y)
   ----- "arr-err-2"
   (APP ρ (Arr (c_x ↦ (λ x c_y) ρ_c O_c) V_f) ([V_x o_x]) blame ρ_2 o_y)]
  
  [(δ ρ op ([V o] ...) A ρ_1 o_a)
   ----- "app-prim"
   (APP ρ op ([V o] ...) A ρ_1 o_a)]
  
  [(δ ρ proc? ([V_f ∅]) #f ρ_1 o_t)
   ----- "app-err"
   (APP ρ V_f ([V o] ...) blame ρ_1 ∅)]
  
  ; poor man's havoc
  [(δ ρ proc? ([(• C ...) ∅]) #t ρ_1 o_t)
   ----- "havoc-1"
   (APP ρ (• C ...) ([V o] ...) (•) ρ_1 ∅)]
  [(δ ρ proc? ([(• C ...) ∅]) #t ρ_1 o_t)
   ----- "havoc-2"
   (APP ρ (• C ...) ([V o] ...) blame ρ_1 ∅)])

;; monitoring
(define-judgment-form scpcf
  #:mode     (MON I I I     O O)
  #:contract (MON ρ C (V o) A ρ)
  [(APP ρ V_p ([V o]) V_t ρ_1 o_t)
   (δ ρ_1 false? ([V_t o_t]) #f ρ_2 o_t′)
   ----- "flat"
   (MON ρ V_p (V o) (refine V V_p) ρ_2)]
  [(APP ρ V_p ([V o]) V_t ρ_1 o_t)
   (δ ρ_1 false? ([V_t o_t]) #t ρ_2 o_t′)
   ----- "flat-fail"
   (MON ρ V_p (V o) blame ρ_2)]
  [(APP ρ V_p ([V o]) blame ρ_1 o)
   ----- "flat-err"
   (MON ρ V_p (V o) blame ρ_1)]
  
  [(δ ρ proc? ([V o]) #f ρ_1 o_t)
   ----- "func/c-fail"
   (MON ρ (c_x ↦ (λ x c_y) ρ_c O_c) (V o) blame ρ_1)]
  [(δ ρ proc? ([V o]) #t ρ_1 o_t)
   ----- "func/c"
   (MON ρ (c_x ↦ (λ x c_y) ρ_c O_c) (V o) (Arr (c_x ↦ (λ x c_y) ρ_c O_c) V) ρ_1)]
  
  [(FC ρ C_1 (V o) V_t ρ_1)
   (δ ρ_1 false? ([V_t ∅]) #f ρ_2 o_t)
   ----- "or/c-left"
   (MON ρ (Or/c C_1 C_2) (V o) (refine V C_1) ρ_2)]
  [(FC ρ C_1 (V o) V_t ρ_1)
   (δ ρ_1 false? ([V_t ∅]) #t ρ_2 o_t)
   (MON ρ_2 C_2 (V o) A ρ_3)
   ----- "or/c-right"
   (MON ρ (Or/c C_1 C_2) (V o) A ρ_3)]
  [(FC ρ C_1 (V o) blame ρ_1)
   ----- "or/c-err"
   (MON ρ (Or/c C_1 C_2) (V o) blame ρ_1)]
  
  [(MON ρ C_1 (V o) V_1 ρ_1)
   (MON ρ_1 C_2 (V_1 o) A ρ_2)
   ----- "and/c"
   (MON ρ (And/c C_1 C_2) (V o) A ρ_2)]
  [(MON ρ C_1 (V o) blame ρ_1)
   ----- "and/c-fail"
   (MON ρ (And/c C_1 C_2) (V o) blame ρ_1)]
  
  [(δ ρ car ([V o]) V_1 ρ_1 o_1)
   (δ ρ_1 cdr ([V o]) V_2 ρ_2 o_2)
   (⇓c ρ_c O_c c_1 C_1)
   (⇓c ρ_c O_c c_2 C_2)
   (MON ρ_2 C_1 (V_1 o_1) V_1′ ρ_3)
   (MON ρ_3 C_2 (V_2 o_2) V_2′ ρ_4)
   ----- "cons/c"
   (MON ρ (Cons/c c_1 c_2 ρ_c O_c) (V o) (Cons V_1′ V_2′) ρ_4)]
  [(δ ρ cons? ([V o]) #f ρ_1 o_t)
   ----- "cons/c-err-1"
   (MON ρ (Cons/c c_1 c_2 ρ_C O_c) (V o) blame ρ_1)]
  [(δ ρ car ([V o]) V_1 ρ_1 o_1)
   (δ ρ_1 cdr ([V o]) V_2 ρ_2 o_2)
   (⇓c ρ_c O_c c_1 C_1)
   (⇓c ρ_c O_c c_2 C_2)
   (MON ρ_2 C_1 (V_1 o_1) blame ρ_3)
   ----- "cons/c-err-2"
   (MON ρ (Cons/c c_1 c_2 ρ_c O_c) (V o) blame ρ_3)]
  [(δ ρ car ([V o]) V_1 ρ_1 o_1)
   (δ ρ_1 cdr ([V o]) V_2 ρ_2 o_2)
   (⇓c ρ_c O_c c_1 C_1)
   (⇓c ρ_c O_c c_2 C_2)
   (MON ρ_2 C_1 (V_1 o_1) V_1′ ρ_3)
   (MON ρ_3 C_2 (V_2 o_2) blame ρ_4)
   ----- "cons/c-err-3"
   (MON ρ (Cons/c c_1 c_2 ρ_c O_c) (V o) blame ρ_4)])

(define-judgment-form scpcf
  #:mode     (δ I I  I           O O O)
  #:contract (δ ρ op ([V o] ...) A ρ o)
  
  ; primitive predicates
  [(δ ρ p? ([V o]) #t ρ ∅)
   (where Proved (proves? V p?))]
  [(δ ρ p? ([V o]) #f ρ ∅)
   (where Refuted (proves? V p?))]
  [(δ ρ p? ([V o]) #t [ρ: ρ [o ↦ p?]] ∅)
   (where Neither (proves? V p?))]
  [(δ ρ p? ([V o]) #f [ρ: ρ [o ↦ (¬ p?)]] ∅)
   (where Neither (proves? V p?))]
  
  ; +
  [(δ ρ + ([m o_m] [n o_n]) (@ + m n) ρ ∅)]
  [(δ ρ + ([V_1 o_1] [V_2 o_2]) blame ρ_1 ∅)
   (δ ρ int? ([V_1 o_1]) #f ρ_1 o_t)]
  [(δ ρ + ([V_1 o_1] [V_2 o_2]) blame ρ_2 ∅)
   (δ ρ int? ([V_1 o_1]) #t ρ_1 o_t1)
   (δ ρ_1 int? ([V_2 o_2]) #f ρ_2 o_t2)]
  [(δ ρ + ([V o_1] [(• C ...) o_2]) (• int?) ρ_2 ∅)
   (δ ρ int? ([V o_1]) #t ρ_1 o_t1)
   (δ ρ_1 int? ([(• C ...) o_2]) #t ρ_2 o_t2)]
  [(δ ρ + ([(• C ...) o_1] [V o_2]) (• int?) ρ_2 ∅)
   (δ ρ int? ([(• C ...) o_1]) #t ρ_1 o_t1)
   (δ ρ_1 int? ([V o_2]) #t ρ_2 o_t2)]
  
  ; add1
  [(δ ρ add1 ([n o]) (@ add1 n) ρ ∅)]
  [(δ ρ add1 ([V o]) blame ρ_1 ∅)
   (δ ρ int? ([V o]) #f ρ_1 o_t)]
  [(δ ρ add1 ([(• C ...) o]) (• int?) ρ_1 ∅)
   (δ ρ int? ([(• C ...) o]) #t ρ_1 o_t)]
  
  ; car, cdr
  [(δ ρ car ([(Cons V_1 V_2) o]) V_1 ρ (acc+ car o))]
  [(δ ρ cdr ([(Cons V_1 V_2) o]) V_2 ρ (acc+ cdr o))]
  [(δ ρ acc ([V o]) blame ρ_1 ∅)
   (δ ρ cons? ([V o]) #f ρ_1 o_t)]
  [(δ ρ acc ([(• C ...) o]) (•) ρ_1 (acc+ acc o))
   (δ ρ cons? ([(• C ...) o]) #t ρ_1 o_t)]
  
  ; cons
  [(δ ρ cons ([V_1 o_1] [V_2 o_2]) (Cons V_1 V_2) ρ ∅)])

;; monitor a flat contract
(define-judgment-form scpcf
  #:mode     (FC I I I     O O)
  #:contract (FC ρ C (V o) A ρ)
  [(APP ρ V_p ([V o]) A ρ_1 o)
   ----- "FC-flat"
   (FC ρ V_p (V o) A ρ_1)]
  [(FC ρ C_1 (V o) A_1 ρ_1)
   (FC ρ_1 C_2 (V o) A_2 ρ_2)
   ----- "FC-or/c"
   (FC ρ (Or/c C_1 C_2) (V o) (OR A_1 A_2) ρ_2)]
  [(FC ρ C_1 (V o) A_1 ρ_1)
   (FC ρ C_2 (V o) A_2 ρ_2)
   ----- "FC-and/c"
   (FC ρ (And/c C_1 C_2) (V o) (AND A_1 A_2) ρ_2)]
  [(δ ρ car ([V o]) V_1 ρ_1 o_1)
   (δ ρ_1 cdr ([V o]) V_2 ρ_2 o_2)
   (⇓c ρ_c O_c c_1 C_1)
   (⇓c ρ_c O_c c_2 C_2)
   (FC ρ_2 C_1 (V_1 o_1) A_1 ρ_3)
   (FC ρ_3 C_2 (V_2 o_2) A_2 ρ_4)
   ----- "FC-cons/c"
   (FC ρ (Cons/c c_1 c_2 ρ_c O_c) (V o) (AND A_1 A_2) ρ_4)]
  [(δ ρ cons? ([V o]) #f ρ_1 o_1)
   ----- "FC-cons/c-fail"
   (FC ρ (Cons/c c_1 c_2 ρ_c O_c) (V o) #f ρ_1)])
(define-metafunction scpcf
  AND : A ... -> A
  [(AND) #t]
  [(AND blame A ...) blame]
  [(AND #f A ...) #f]
  [(AND A_1 A ...) (AND A ...)])
(define-metafunction scpcf
  OR : A ... -> A
  [(OR) #f]
  [(OR #f A ...) (OR A ...)]
  [(OR A A_1 ...) A])
      
(define-metafunction scpcf
  acc+ : acc o -> o
  [(acc+ acc (acc_1 ... x)) (acc acc_1 ... x)]
  [(acc+ acc o) ∅])

(define-metafunction scpcf
  default-o : o {x ...} o -> o
  [(default-o (acc ... x) {z ... x y ...} o) (acc ... x)]
  [(default-o o_1 {x ...} o_2) o_2])

(define-metafunction scpcf
  dom : ([x ↦ any] ...) -> {x ...}
  [(dom ([x ↦ any] ...)) {x ...}])

(define-metafunction scpcf
  remove-dups : {any ...} -> {any ...}
  [(remove-dups {any_1 ... any any_2 ... any any_3 ...})
   (remove-dups {any_1 ... any any_2 ... any_3 ...})]
  [(remove-dups any) any])

(define-metafunction scpcf
  close : v ρ O -> V
  [(close b ρ O) b]
  [(close • ρ O) (•)]
  [(close (λ x e) ρ O) ((λ x e) ρ O)])

(define-metafunction/extension subst1 scpcf
  subst : e x any -> e
  [(subst • x any) •])
(define-metafunction/extension subst/c1 scpcf
  subst/c : c x any -> c)

(define (s-map f xs)
  (set->list (list->set (map f xs))))

;; checks whether value proves contract
(define-metafunction scpcf
  proves? : V C -> Proved?
  [(proves? n int?) Proved]
  [(proves? n p?) Refuted]
  [(proves? #f false?) Proved]
  [(proves? bool p?) Refuted]
  [(proves? PROC proc?) Proved]
  [(proves? PROC p?) Refuted]
  [(proves? (Cons V_1 V_2) cons?) Proved]
  [(proves? (Cons V_1 V_2) p?) Refuted]
  [(proves? V (Or/c C_1 ... C C_2 ...))
   Proved
   (where Proved (proves? V C))]
  [(proves? V (And/c C_1 ... C C_2 ...))
   Refuted
   (where Refuted (proves? V C))]
  [(proves? V ((λ x (false? (p? x))) ρ O))
   Proved
   (where Refuted (proves? V p?))]
  [(proves? V ((λ x (false? (p? x))) ρ O))
   Refuted
   (where Proved (proves? V p?))]
  [(proves? (• C_1 ... C C_2 ...) C) Proved]
  [(proves? (• C_1 ... ((λ x (false? (p? x))) ρ O) C_2 ...) p?) Refuted]
  [(proves? V C) Neither])

;; refines a value with given contract.
;; PRECON: (proves? V C) = Neither
;; POSTCON: (refine V C) ⊑ V
(define-metafunction scpcf
  refine : V C -> V
  [(refine (• C ...) (Cons c_1 c_2 ρ O))
   (Cons (refine (•) C_1) (refine (•) C_2))
   (where (C_1) ,(judgment-holds (⇓c ρ O c_1 C) C))
   (where (C_2) ,(judgment-holds (⇓c ρ O c_2 C) C))]
  [(refine (Cons V_1 V_2) (Cons c_1 c_2 ρ O))
   (Cons (refine V_1 C_1) (refine V_2 C_2))
   (where (C_1) ,(judgment-holds (⇓c ρ O c_1 C) C))
   (where (C_2) ,(judgment-holds (⇓c ρ O c_2 C) C))]
  [(refine (• C ...) cons?) (Cons (•) (•))]
  [(refine (• C ...) false?) #f]
  [(refine (• C_1 ...) C) (• C C_1 ...)]
  [(refine V C) V])

;; refines values refered to by the first environment from more precisee
;; information from second environment
(define-metafunction scpcf
  ρ-upd : ρ ρ -> ρ
  [(ρ-upd ρ ()) ρ]
  [(ρ-upd (any ... [x ↦ V] any_1 ...) ([x ↦ V_1] any_2 ...))
   (ρ-upd (any ... [x ↦ (V⊓ V V_1)] any_1 ...) (any_2 ...))]
  [(ρ-upd ρ (any_1 any ...)) (ρ-upd ρ (any ...))])

;; refines value at given path in environment
;; PRECON: path corresponds to some object from environment
;; POSTCON: (ρ: ρ [o ↦ φ]) ⊑ ρ
(define-metafunction scpcf
  ρ: : ρ [o ↦ φ] -> ρ
  [(ρ: (any ... [x ↦ V] any_1 ...) [(acc ... x) ↦ φ])
   (any ... [x ↦ (V-upd V (acc ...) φ)] any_1 ...)]
  [(ρ: ρ [∅ ↦ φ]) ρ])

;; extends environment
(define-metafunction scpcf
  ρ+ : ρ [x ↦ V] -> ρ
  [(ρ+ (any ... [x ↦ V_1] any_1 ...) [x ↦ V]) ([x ↦ V] any ... any_1 ...)]
  [(ρ+ (any ...) [x ↦ V]) ([x ↦ V] any ...)])

;; restricts environment
(define-metafunction scpcf
  ρ- : ρ x -> ρ
  [(ρ- (any ... [x ↦ V] any_1 ...) x) (any ... any_1 ...)])

;; POSTCON: (V-upd V (acc ...) φ) ⊑ V
(define-metafunction scpcf
  V-upd : V (acc ...) φ -> V
  [(V-upd V () p?) (refine V p?)]
  [(V-upd V () (¬ p?)) (refine V ((λ X (false? (p? X))) () ()))]
  [(V-upd (Cons V_1 V_2) (car acc ...) φ)
   (Cons (V-upd V_1 (acc ...) φ) V_2)]
  [(V-upd (Cons V_1 V_2) (cdr acc ...) φ)
   (Cons V_1 (V-upd V_2 (acc ...) φ))]
  ; give up, lose precision
  [(V-upd V (acc ...) φ) V])

(define-metafunction scpcf
  ev : e -> {EA ...}
  [(ev e)
   (remove-dups ((A->EA A) ...))
   (where (A ...) ,(judgment-holds (⇓ () () e A ρ o) A))])
(define-metafunction scpcf
  A->EA : A -> EA
  [(A->EA (•)) •]
  [(A->EA V) function (where Proved (proves? V proc?))]
  [(A->EA (Cons V_1 V_2)) (Cons (A->EA V_1) (A->EA V_2))]
  [(A->EA A) A])

(define-metafunction scpcf
  @ : any V ... -> V
  [(@ + m n) ,(+ (term m) (term n))]
  [(@ add1 n) ,(add1 (term n))])