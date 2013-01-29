#lang racket
(require
 redex
 (only-in "lang-simple.rkt" cpcf :: ! \\
          [AND AND′] [OR OR′] [subst subst1] [subst/c subst/c1]))
(provide
 scpcf ev ⇓ ⇓c APP MON FC δ ∆ close
 refine proves? dom σ: var-not-in not-equal? !)
         
(define-extended-language scpcf cpcf
  [v .... •]
  [b .... s]
  [o1 .... str-len]
  [p? .... true? str?]
  [s string]
  
  ; environments
  [ρ ([x ↦ V] ...)]
  [σ ([l ↦ V] ...)]
  [φ p? (¬ p?)]
  
  ; closed value ∪ pointer
  [V b
     ((λ x e) ρ)
     (Arr (c ↦ (λ x c) ρ) V)
     (Cons V V)
     l
     (★ C ...)]
  [W b ((λ x e) ρ) (Arr (c ↦ (λ x c) ρ) V) (Cons V V) (★ C ...)]
  [EA function n #t #f s (Cons EA EA) (• C ...) • blame]
      
  ; evaluated contract
  [C V
     (c ↦ (λ x c) ρ)
     (Cons/c c c ρ)
     (Or/c C C)
     (And/c C C)]
  [Proved? Proved Refuted Neither]
  
  ; convenient patterns
  [bool #t #f]
  [PROC ((λ x e) ρ) (Arr (c ↦ (λ x c) ρ) V) op]
  [l variable-not-otherwise-mentioned])

;; evaluation
(define-judgment-form scpcf
  #:mode     (⇓ I I I O O)
  #:contract (⇓ σ ρ e A σ)
  [----- "blame"
   (⇓ σ ρ blame blame σ)]
  [(where l (var-not-in σ L))
   ----- "val-•"
   (⇓ σ ρ • l [:: σ [l ↦ (★)]])]
  [(side-condition (not-equal? v •))
   ----- "val"
   (⇓ σ ρ v [close v ρ] σ)]
  [----- "var"
   (⇓ σ ρ x [! ρ x] σ)]
  
  [(⇓ σ ρ e V_t σ_1)
   (δ σ_1 false? [V_t] #f σ_2)
   (⇓ σ_2 ρ e_1 A σ_3)
   ----- "if-true"
   (⇓ σ ρ (if e e_1 e_2) A σ_3)]
  [(⇓ σ ρ e V_t σ_1)
   (δ σ_1 false? [V_t] #t σ_2)
   (⇓ σ_2 ρ e_2 A σ_3)
   ----- "if-false"
   (⇓ σ ρ (if e e_1 e_2) A σ_3)]
  [(⇓ σ ρ e blame σ_1)
   ----- "if-err"
   (⇓ σ ρ (if e e_1 e_2) blame σ_1)]
  
  [(⇓ σ ρ e_f V_f σ_1)
   (⇓ σ_1 ρ e_x V_x σ_2)
   (APP σ_2 V_f [V_x] A σ_3)
   ----- "app-1"
   (⇓ σ ρ (e_f e_x) A σ_3)]
  [(⇓ σ ρ e_f V_f σ_1)
   (⇓ σ_1 ρ e_x V_x σ_2)
   (⇓ σ_2 ρ e_y V_y σ_3)
   (APP σ_3 V_f [V_x V_y] A σ_4)
   ----- "app-2"
   (⇓ σ ρ (e_f e_x e_y) A σ_4)]
  [(⇓ σ ρ e_f blame σ_1)
   ----- "app-err-1"
   (⇓ σ ρ (e_f e_x ...) blame σ_1)]
  [(⇓ σ ρ e_f V_f σ_1)
   (⇓ σ_1 ρ e_x blame σ_2)
   ----- "app-err-2"
   (⇓ σ ρ (e_f e_x e_y ...) blame σ_2)]
  [(⇓ σ ρ e_f V_f σ_1)
   (⇓ σ_1 ρ e_x V_x σ_2)
   (⇓ σ_2 ρ e_y blame σ_3)
   ----- "app-err-3"
   (⇓ σ ρ (e_f e_x e_y) blame σ_3)]
  
  [(⇓c σ ρ c C σ_1)
   (⇓ σ_1 ρ e V σ_2)
   (MON σ_2 C V A σ_3)
   ----- "mon"
   (⇓ σ ρ (mon c e) A σ_3)]
  [(⇓c σ ρ c C σ_1)
   (⇓ σ_1 ρ e blame σ_2)
   ----- "mon-err"
   (⇓ σ ρ (mon c e) blame σ_2)])

;; contract evaluation
(define-judgment-form scpcf
  #:mode     (⇓c I I I O O)
  #:contract (⇓c σ ρ c C σ)
  [(⇓ σ ρ v V σ_1)
   ----- "flat"
   (⇓c σ ρ (flat v) V σ_1)]
  
  [----- "func/c"
   (⇓c σ ρ (c_x ↦ (λ x c_y)) (c_x ↦ (λ x c_y) ρ) σ)]
   
  [(⇓c σ ρ c_1 C_1 σ_1)
   (⇓c σ_1 ρ c_2 C_2 σ_2)
   ----- "and/c"
   (⇓c σ ρ (and/c c_1 c_2) (And/c C_1 C_2) σ_2)]
  
  [(⇓c σ ρ c_1 C_1 σ_1)
   (⇓c σ_1 ρ c_2 C_2 σ_2)
   ----- "or/c"
   (⇓c σ ρ (or/c c_1 c_2) (Or/c C_1 C_2) σ_2)]
  
  [----- "cons/c"
   (⇓c σ ρ (cons/c c_1 c_2) (Cons/c c_1 c_2 ρ) σ)]
  
  [(⇓c σ ρ [subst/c c x (μ x c)] C σ_1)
   ----- "μ/c"
   (⇓c σ ρ (μ x c) C σ_1)])

;; application
(define-judgment-form scpcf
  #:mode     (APP I I I       O O)
  #:contract (APP σ V [V ...] A σ)
  
  [(⇓ σ [:: ρ [x ↦ V]] e A σ_1)
   ----- "app-λ"
   (APP σ ((λ x e) ρ) [V] A σ_1)]
   
  [(⇓c σ ρ c_x C_x σ_1)
   (MON σ_1 C_x V_x V_x′ σ_2)
   (APP σ_2 V_f [V_x′] V_y σ_3)
   (⇓c σ_3 [:: ρ [x ↦ V_x′]] c_y C_y σ_4)
   (MON σ_4 C_y V_y A σ_5)
   ----- "app-arr"
   (APP σ (Arr (c_x ↦ (λ x c_y) ρ) V_f) [V_x] A σ_5)]
  [(⇓c σ ρ c_x C_x σ_1)
   (MON σ_1 C_x V_x blame σ_2)
   ----- "arr-err-1"
   (APP σ (Arr (c_x ↦ (λ x c_y) ρ) V_f) [V_x] blame σ_2)]
  [(⇓c σ ρ c_x C_x σ_1)
   (MON σ_1 C_x V_x V_x′ σ_2)
   (APP σ_2 V_f [V_x′] blame σ_3)
   ----- "arr-err-2"
   (APP σ (Arr (c_x ↦ (λ x c_y) ρ) V_f) [V_x] blame σ_3)]
  
  [(δ σ op [V ...] A σ_1)
   ----- "app-prim"
   (APP σ op [V ...] A σ_1)]
  
  [(δ σ proc? [V_f] #f σ_1)
   ----- "app-err"
   (APP σ V_f [V ...] blame σ_1)]
  
  [(APP σ [! σ l] [V ...] A σ_1)
   ----- "app-l"
   (APP σ l [V ...] A σ_1)]
  
  ; poor man's havoc
  [(δ σ proc? [(★ C ...)] #t σ_1)
   ----- "havoc-1"
   (APP σ (★ C ...) [V ...] (★) σ_1)]
  [(δ σ proc? [(★ C ...)] #t σ_1)
   ----- "havoc-2"
   (APP σ (★ C ...) [V ...] blame σ_1)])

;; monitoring
(define-judgment-form scpcf
  #:mode     (MON I I I O O)
  #:contract (MON σ C V A σ)
  [(APP σ V_p [V] V_t σ_1)
   (δ σ_1 false? [V_t] #f σ_2)
   ----- "flat-ok"
   (MON σ V_p V [refine V V_p] σ_2)]
  [(APP σ V_p [V] V_t σ_1)
   (δ σ_1 false? [V_t] #t σ_2)
   ----- "flat-fail"
   (MON σ V_p V blame σ_2)]
  [(APP σ V_p [V] blame σ_1)
   ----- "flat-err"
   (MON σ V_p V blame σ_1)]
  
  [(δ σ proc? [V] #f σ_1)
   ----- "func/c-fail"
   (MON σ (c_x ↦ (λ x c_y) ρ) V blame σ_1)]
  [(δ σ proc? [V] #t σ_1)
   ----- "func/c"
   (MON σ (c_x ↦ (λ x c_y) ρ) V (Arr (c_x ↦ (λ x c_y) ρ) V) σ_1)]
  
  [(FC σ C_1 V V_t σ_1)
   (δ σ_1 false? [V_t] #f σ_2)
   ----- "or/c-left"
   (MON σ (Or/c C_1 C_2) V [refine V C_1] σ_2)]
  [(FC σ C_1 V V_t σ_1)
   (δ σ_1 false? [V_t] #t σ_2)
   (MON σ_2 C_2 V A σ_3)
   ----- "or/c-right"
   (MON σ (Or/c C_1 C_2) V A σ_3)]
  [(FC σ C_1 V blame σ_1)
   ----- "or/c-err"
   (MON σ (Or/c C_1 C_2) V blame σ_1)]
  
  [(MON σ C_1 V V_1 σ_1)
   (MON σ_1 C_2 V_1 A σ_2)
   ----- "and/c"
   (MON σ (And/c C_1 C_2) V A σ_2)]
  [(MON σ C_1 V blame σ_1)
   ----- "and/c-fail"
   (MON σ (And/c C_1 C_2) V blame σ_1)]
  
  [(δ σ car [V] V_1 σ_1)
   (δ σ_1 cdr [V] V_2 σ_2)
   (⇓c σ_2 ρ c_1 C_1 σ_3)
   (⇓c σ_3 ρ c_2 C_2 σ_4)
   (MON σ_4 C_1 V_1 V_1′ σ_5)
   (MON σ_5 C_2 V_2 V_2′ σ_6)
   ----- "cons/c"
   (MON σ (Cons/c c_1 c_2 ρ) V (Cons V_1′ V_2′) σ_6)]
  [(δ σ cons? [V] #f σ_1)
   ----- "cons/c-err-1"
   (MON σ (Cons/c c_1 c_2 ρ) V blame σ_1)]
  [(δ σ car [V] V_1 σ_1)
   (δ σ_1 cdr [V] V_2 σ_2)
   (⇓c σ_2 ρ c_1 C_1 σ_3)
   (⇓c σ_3 ρ c_2 C_2 σ_4)
   (MON σ_4 C_1 V_1 blame σ_5)
   ----- "cons/c-err-2"
   (MON σ (Cons/c c_1 c_2 ρ) V blame σ_5)]
  [(δ σ car [V] V_1 σ_1)
   (δ σ_1 cdr [V] V_2 σ_2)
   (⇓c σ_2 ρ c_1 C_1 σ_3)
   (⇓c σ_3 ρ c_2 C_2 σ_4)
   (MON σ_4 C_1 V_1 V_1′ σ_5)
   (MON σ_5 C_2 V_2 blame σ_6)
   ----- "cons/c-err-3"
   (MON σ (Cons/c c_1 c_2 ρ) V blame σ_5)])

(define-judgment-form scpcf
  #:mode     (δ I I  I       O O)
  #:contract (δ σ op [V ...] A σ)
  
  ; primitive predicates
  [(δ σ p? [[! σ l]] #t σ_1)
   ------ "pred-l-ok"
   (δ σ p? [l] #t [σ: σ_1 [l ↦ p?]])]
  [(δ σ p? [[! σ l]] #f σ_1)
   ------ "pred-l-fail"
   (δ σ p? [l] #f [σ: σ_1 [l ↦ (¬ p?)]])]
  
  [(where Proved (proves? W p?))
   ----- "pred-ok"
   (δ σ p? [W] #t σ)]
  [(where Refuted (proves? W p?))
   ----- "pred-fail"
   (δ σ p? [W] #f σ)]
  [(where Neither (proves? W p?))
   ----- "pred-assumed-ok"
   (δ σ p? [W] #t σ)]
  [(where Neither (proves? W p?))
   ----- "pred-assumed-fail"
   (δ σ p? [W] #f σ)]
  
  ; +
  [(δ σ + [m n] (∆ + m n) σ)]
  [(δ σ + [V_1 V_2] blame σ_1)
   (δ σ int? [V_1] #f σ_1)]
  [(δ σ + [V_1 V_2] blame σ_2)
   (δ σ int? [V_1] #t σ_1)
   (δ σ_1 int? [V_2] #f σ_2)]
  [(δ σ + [V_1 V_2] (★ int?) σ_2)
   (δ σ int? [V_1] #t σ_1)
   (δ σ_1 int? [V_2] #t σ_2)
   (side-condition (OR (not (n? V_1)) (not (n? V_2))))]
  
  ; add1
  [----- "add1-n"
   (δ σ add1 [n] (∆ add1 n) σ)]
  [(δ σ int? [V] #f σ_1)
   ----- "add1-fail"
   (δ σ add1 [V] blame σ_1)]
  [(side-condition (not (n? V)))
   (δ σ int? [V] #t σ_1)
   ----- "add1-assumed-ok"
   (δ σ add1 [V] (★ int?) σ_1)]
  
  ; car, cdr
  [----- "car-ok"
   (δ σ car [(Cons V_1 V_2)] V_1 σ)]
  [(δ σ cdr [(Cons V_1 V_2)] V_2 σ)]
  [(δ σ cons? [V] #f σ_1)
   ----- "acc-fail"
   (δ σ acc [V] blame σ_1)]
  [(δ σ cons? [l] #t σ_1)
   (where (Cons V_1 V_2) (! σ_1 l))
   ----- "car-l-assumed-ok"
   (δ σ car [l] V_1 σ_1)]
  [(δ σ cons? [(★ C ...)] #t σ_1)
   ----- "car-★-assumed-ok"
   (δ σ car [(★ C ...)] (★) σ_1)]
  [(δ σ cons? [l] #t σ_1)
   (where (Cons V_1 V_2) (! σ_1 l))
   ----- "cdr-l-assumed-ok"
   (δ σ cdr [l] V_2 σ_1)]
  [(δ σ cons? [(★ C ...)] #t σ_1)
   ----- "cdr-★-assumed-ok"
   (δ σ cdr [(★ C ...)] (★) σ_1)]
  
  ; cons
  [(δ σ cons [V_1 V_2] (Cons V_1 V_2) σ)]
  
  ; str-len
  [(δ σ str-len [s] (∆ str-len s) σ)]
  [(δ σ str-len [V] blame σ_1)
   (δ σ str? [V] #f σ_1)]
  [(δ σ str-len [V] (★ int?) σ_1)
   (δ σ str? [V] #t σ_1)
   (side-condition (not (s? V)))])

;; monitor a flat contract
(define-judgment-form scpcf
  #:mode     (FC I I I O O)
  #:contract (FC σ C V A σ)
  [(APP σ V_p [V] A σ_1)
   ----- "FC-flat"
   (FC σ V_p V A σ_1)]
  [(FC σ C_1 V A_1 σ_1)
   (FC σ_1 C_2 V A_2 σ_2)
   ----- "FC-or/c"
   (FC σ (Or/c C_1 C_2) V (OR A_1 A_2) σ_2)]
  [(FC σ C_1 V A_1 σ_1)
   (FC σ_1 C_2 V A_2 σ_2)
   ----- "FC-and/c"
   (FC σ (And/c C_1 C_2) V (AND A_1 A_2) σ_2)]
  [(δ σ car [V] V_1 σ_1)
   (δ σ_1 cdr [V] V_2 σ_2)
   (⇓c σ_2 ρ c_1 C_1 σ_3)
   (⇓c σ_3 ρ c_2 C_2 σ_4)
   (FC σ_4 C_1 V_1 A_1 σ_5)
   (FC σ_5 C_2 V_2 A_2 σ_6)
   ----- "FC-cons/c"
   (FC σ (Cons/c c_1 c_2 ρ) V (AND A_1 A_2) σ_6)]
  [(δ σ cons? [V] #f σ_1)
   ----- "FC-cons/c-fail"
   (FC σ (Cons/c c_1 c_2 ρ) V #f σ_1)])

(define-metafunction/extension AND′ scpcf
  AND : A ... -> A)
(define-metafunction/extension OR′ scpcf
  OR : A ... -> A)

(define-metafunction scpcf
  dom : ([any ↦ any] ...) -> {any ...}
  [(dom ([any_k ↦ any_v] ...)) {any_k ...}])

(define-metafunction scpcf
  remove-dups : {any ...} -> {any ...}
  [(remove-dups {any_1 ... any any_2 ... any any_3 ...})
   (remove-dups {any_1 ... any any_2 ... any_3 ...})]
  [(remove-dups any) any])

(define-metafunction scpcf
  close : v ρ -> V
  [(close b ρ) b]
  [(close (λ x e) ρ) ((λ x e) ρ)])

(define-metafunction/extension subst1 scpcf
  subst : e x any -> e
  [(subst • x any) •])
(define-metafunction/extension subst/c1 scpcf
  subst/c : c x any -> c)

(define (s-map f xs)
  (set->list (list->set (map f xs))))

;; checks whether value proves contract
(define-metafunction scpcf
  proves? : W C -> Proved?
  [(proves? V ((λ x #t) ρ)) Proved]
  [(proves? s str?) Proved]
  [(proves? s p?) Refuted]
  [(proves? n int?) Proved]
  [(proves? n p?) Refuted]
  [(proves? #f false?) Proved]
  [(proves? #f p?) Refuted]
  [(proves? #t true?) Proved]
  [(proves? #t p?) Refuted]
  [(proves? PROC proc?) Proved]
  [(proves? PROC p?) Refuted]
  [(proves? (Cons V_1 V_2) cons?) Proved]
  [(proves? (Cons V_1 V_2) p?) Refuted]
  [(proves? V (Or/c C_1 ... C C_2 ...)) Proved (where Proved (proves? V C))]
  [(proves? V (Or/c C ...)) Refuted (where (Refuted ...) ((proves? V C) ...))]
  [(proves? V (And/c C_1 ... C C_2 ...)) Refuted (where Refuted (proves? V C))]
  [(proves? V (And/c C ...)) Proved (where (Proved ...) ((proves? V C) ...))]
  [(proves? V ((λ x (false? (p? x))) ρ)) Proved (where Refuted (proves? V p?))]
  [(proves? V ((λ x (false? (p? x))) ρ)) Refuted (where Proved (proves? V p?))]
  [(proves? (★ C_1 ... C C_2 ...) C) Proved]
  [(proves? (★ C_1 ... ((λ x (false? (p? x))) ρ) C_2 ...) p?) Refuted]
  [(proves? (★ C_1 ... p? C_2 ...) p?_1) Refuted] ; p? ≠ p?_1
  [(proves? V C) Neither])

;; refines a value with given contract.
;; PRECON: (proves? V C) = Neither
;; POSTCON: (refine V C) ⊑ V
(define-metafunction scpcf
  refine : V C -> V
  [(refine W C) W (where Proved (proves? W C))]
  [(refine (★ C ...) (Cons/c c_1 c_2 ρ))
   (Cons (refine (★) C_1) (refine (★) C_2)) ; FIXME wrong
   (where (C_1) ,(judgment-holds (⇓c [] ρ c_1 C σ) C))
   (where (C_2) ,(judgment-holds (⇓c [] ρ c_2 C σ) C))]
  [(refine (Cons V_1 V_2) (Cons/c c_1 c_2 ρ))
   (Cons (refine V_1 C_1) (refine V_2 C_2)) ; FIXME wrong
   (where (C_1) ,(judgment-holds (⇓c [] ρ c_1 C σ) C))
   (where (C_2) ,(judgment-holds (⇓c [] ρ c_2 C σ) C))]
  [(refine (★ C ...) cons?) (Cons (★) (★))]
  [(refine (★ C ...) false?) #f]
  [(refine (★ C ...) true?) #t]
  [(refine (★ C_1 ...) C) (★ C C_1 ...)]
  [(refine V C) V])

;; refines value at given path in environment
;; POSTCON: (ρ: ρ [o ↦ φ]) ⊑ ρ
(define-metafunction scpcf
  σ: : σ [l ↦ φ] -> σ
  [(σ: (any ... [l ↦ (★ C ...)] any_1 ...) [l ↦ cons?])
   ([l ↦ (Cons l_1 l_2)] [l_1 ↦ (★)] [l_2 ↦ (★)] any ... any_1 ...)
   (where (l_1 l_2) ,(variables-not-in (term (any ... any_1 ... l)) (term (L L))))]
  [(σ: (any ... [l ↦ V] any_1 ...) [l ↦ p?])
   (any ... [l ↦ (refine V p?)] any_1 ...)]
  [(σ: (any ... [l ↦ V] any_1 ...) [l ↦ (¬ p?)])
   (any ... [l ↦ (refine V ((λ X (false? (p? X))) ()))] any_1 ...)])

(define-metafunction scpcf
  ev : e -> {EA ...}
  [(ev e)
   (remove-dups ((A->EA σ A) ...))
   (where ((A σ) ...) ,(judgment-holds (⇓ () () e A σ) (A σ)))])
(define-metafunction scpcf
  A->EA : σ A -> EA
  [(A->EA σ l) (A->EA σ [! σ l])]
  [(A->EA σ (★)) •]
  [(A->EA σ (★ C ...)) (• C ...)]
  [(A->EA σ V) function (where Proved (proves? V proc?))]
  [(A->EA σ (Cons V_1 V_2)) (Cons (A->EA σ V_1) (A->EA σ V_2))]
  [(A->EA σ A) A])

(define-metafunction scpcf
  ∆ : any V ... -> V
  [(∆ + m n) ,(+ (term m) (term n))]
  [(∆ add1 n) ,(add1 (term n))]
  [(∆ str-len s) ,(string-length (term s))])

(define-metafunction scpcf
  var-not-in : any x -> x
  [(var-not-in any x) ,(variable-not-in (term any) (term x))])

(define-metafunction scpcf
  not-equal? : any any -> #t or #f
  [(not-equal? any any) #f]
  [(not-equal? any any_1) #t])

(define-metafunction scpcf
  n? : any -> #t or #f
  [(n? n) #t] [(n? any) #f])
(define-metafunction scpcf
  s? : any -> #t or #f
  [(s? s) #t] [(s? any) #f])
(define-metafunction scpcf
  not : any -> #t or #f
  [(not #f) #t] [(not any) #f])