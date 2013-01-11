#lang racket
(require redex)

(provide
 cpcf
 ⇓ ⇓c APP MON ev
 close ! :: subst subst/c FC AND OR)

(define-language cpcf
  [e a
     x
     (e e ...)
     (if e e e)
     (μ x e)
     (mon c e)]
  [a v blame]
  [v (λ x e) b]
  [b n #t #f op]
  [op o1 o2]
  [o1 p? add1 acc]
  [p? int? false? proc? cons?]
  [acc car cdr]
  [o2 cons +]
  [(m n) integer]
  [(x y z) variable-not-otherwise-mentioned]
  
  [c (flat e) (c ↦ (λ x c)) (or/c c c) (and/c c c) (cons/c c c) (μ x c) x]
  
  ; closed value
  [V b ((λ x e) ρ) (Arr (c ↦ (λ x c) ρ) V) (Cons V V)]
  [A V blame]
  [EA function b blame (Cons EA EA)]
  
  ; evaluated contract
  [D (Flat V) (c ↦ (λ x c) ρ) (Or/c c c ρ) (And/c D D) (Cons/c D D)]
  [Dns D blame]
  
  ; environment
  [ρ ([x ↦ V] ...)])

;; evaluation
(define-judgment-form cpcf
  #:mode     (⇓ I I O)
  #:contract (⇓ ρ e A)
  [----- "blame"
   (⇓ ρ blame blame)]
  [----- "val"
   (⇓ ρ v [close v ρ])]
  [----- "var"
   (⇓ ρ x [! ρ x])]
  
  [(⇓ ρ e V)
   (where #f (δ false? V))
   (⇓ ρ e_1 A)
   ----- "if-true"
   (⇓ ρ (if e e_1 e_2) A)]
  [(⇓ ρ e #f)
   (⇓ ρ e_2 A)
   ----- "if-false"
   (⇓ ρ (if e e_1 e_2) A)]
  [(⇓ ρ e blame)
   ----- "if-err"
   (⇓ ρ (if e e_1 e_2) blame)]
  
  [(⇓ ρ e_f V_f)
   (⇓ ρ e_x V_x) ...
   ----- "app"
   (⇓ ρ (e_f e_x ...) [APP V_f V_x ...])]
  [(⇓ ρ e_1 V_1) ...
   (⇓ ρ e_i blame)
   ----- "app-err"
   (⇓ ρ (e_1 ... e_i e_i+1 ...) blame)]
  
  [(⇓ ρ [subst e x (μ x e)] A)
   ----- "μ"
   (⇓ ρ (μ x e) A)]
  
  [(⇓c ρ c D)
   (⇓ ρ e V)
   ----- "mon"
   (⇓ ρ (mon c e) [MON D V])]
  [(⇓c ρ c blame)
   ----- "mon-err-c"
   (⇓ ρ (mon c e) blame)]
  [(⇓c ρ c D)
   (⇓ ρ e blame)
   ----- "mon-err-e"
   (⇓ ρ (mon c e) blame)])

;; contract evaluation
(define-judgment-form cpcf
  #:mode     (⇓c I I O)
  #:contract (⇓c ρ c Dns)
  [(⇓ ρ e V)
   ----- "flat"
   (⇓c ρ (flat e) (Flat V))]
  [(⇓ ρ e blame)
   ----- "flat-err"
   (⇓c ρ (flat e) blame)]
  
  [----- "func/c"
   (⇓c ρ (c_x ↦ (λ x c_y)) (c_x ↦ (λ x c_y) ρ))]
  
  [----- "or/c"
   (⇓c ρ (or/c c_1 c_2) (Or/c c_1 c_2 ρ))]
  
  [(⇓c ρ c_1 D_1)
   (⇓c ρ c_2 D_2)
   ----- "and/c"
   (⇓c ρ (and/c c_1 c_2) (And/c D_1 D_2))]
  [(⇓c ρ c_1 blame)
   ----- "and/c-err-1"
   (⇓c ρ (and/c c_1 c_2) blame)]
  [(⇓c ρ c_1 D_1)
   (⇓c ρ c_2 blame)
   ----- "and/c-err-2"
   (⇓c ρ (and/c c_1 c_2) blame)]
  
  [(⇓c ρ c_1 D_1)
   (⇓c ρ c_2 D_2)
   ----- "cons/c"
   (⇓c ρ (cons/c c_1 c_2) (Cons/c D_1 D_2))]
  [(⇓c ρ c_1 blame)
   ----- "cons/c-err-1"
   (⇓c ρ (cons/c c_1 c_2) blame)]
  [(⇓c ρ c_1 D_1)
   (⇓c ρ c_2 blame)
   ----- "cons/c-err-2"
   (⇓c ρ (cons/c c_1 c_2) blame)]
  
  [(⇓c ρ [subst/c c x (μ x c)] Dns)
   ---- "μ/c"
   (⇓c ρ (μ x c) Dns)])
  
;; application
(define-metafunction cpcf
  APP : V V ... -> A
  [(APP ((λ x e_y) ρ) V_x)
   A
   (where (A) ,(judgment-holds (⇓ [:: ρ (x ↦ V_x)] e_y A) A))]
  [(APP (Arr (c_x ↦ (λ x c_y) ρ) V_f) V_x)
   A
   (where (D_x) ,(judgment-holds (⇓c ρ c_x D) D))
   (where V_x′ (MON D_x V_x))
   (where V_y (APP V_f V_x′))
   (where (D_y) ,(judgment-holds (⇓c [:: ρ [x ↦ V_x′]] c_y D) D))
   (where A (MON D_y V_y))]
  [(APP op V_x ...) (δ op V_x ...)])

;; monitoring
(define-metafunction cpcf
  MON : D A -> A
  ; flat
  [(MON (Flat V_p) V) blame (where #f (APP V_p V))]
  [(MON (Flat V_p) V) blame (where blame (APP V_p V))]
  [(MON (Flat V_p) V) V]
  ; func
  [(MON (c_x ↦ (λ x c_y) ρ) V) blame (where #f (δ proc? V))]
  [(MON (c_x ↦ (λ x c_y) ρ) V) (Arr (c_x ↦ (λ x c_y) ρ) V)]
  ; or/c
  [(MON (Or/c c_1 c_2 ρ) V)
   V
   (where (V_p) ,(judgment-holds (⇓ ρ (FC c_1) V) V))
   (where V_t (APP V_p V))
   (where #f (δ false? V_t))]
  [(MON (Or/c c_1 c_2 ρ) V)
   (MON D_2 V)
   (where (V_p) ,(judgment-holds (⇓ ρ (FC c_1) V) V))
   (where #f (APP V_p V))
   (where (D_2) ,(judgment-holds (⇓c ρ c_2 D) D))]
  ; and/c
  [(MON (And/c D_1 D_2) V) (MON D_2 (MON D_1 V))]
  ; cons/c
  [(MON (Cons/c D_1 D_2) (Cons V_1 V_2))
   (Cons V_1′ V_2′)
   (where V_1′ (MON D_1 V_1))
   (where V_2′ (MON D_2 V_2))]
  [(MON (Cons c_1 c_2 ρ) V) blame]
  ; propagate blame
  [(MON D blame) blame])

;; close value
(define-metafunction cpcf
  close : v ρ -> V
  [(close b ρ) b]
  [(close (λ x e) ρ) ((λ x e) ρ)])

;; environment lookup
(define-metafunction cpcf
  ! : ([any ↦ any] ...) any -> any
  [(! (any_1 ... [any_k ↦ any_v] any_2 ...) any_k) any_v])
;; environment update
(define-metafunction cpcf
  :: : ([any ↦ any] ...) [any ↦ any] -> ([any ↦ any] ...)
  [(:: (any_1 ... [any_k ↦ any_v] any_n ...) [any_k ↦ any_u])
   (any_1 ... [any_k ↦ any_u] any_n ...)]
  [(:: (any ...) [any_k ↦ any_v]) ([any_k ↦ any_v] any ...)])

;; substitution, assume α-renamed
(define-metafunction cpcf
  subst : e x any -> e
  [(subst (λ x e) x any) (λ x e)]
  [(subst (λ z e) x any) (λ z (subst e x any))]
  [(subst a x any) a]
  [(subst x x any) any]
  [(subst x z any) x]
  [(subst (e ...) x any) ((subst e x any) ...)]
  [(subst (if e ...) x any) (if (subst e x any) ...)]
  [(subst (μ x e) x any) (μ x e)]
  [(subst (μ z e) x any) (μ z (subst e x any))]
  [(subst (mon c e) x any)
   (mon (subst/c c x any) (subst e x any))])
(define-metafunction cpcf
  subst/c : c x any -> c
  [(subst/c (flat e) x any) (flat (subst e x any))]
  [(subst/c (c_1 ↦ (λ x c_2)) x any)
   ((subst/c c_1 x any) ↦ (λ x c_2))]
  [(subst/c (c_1 ↦ (λ z c_2)) x any)
   ((subst/c c_1 x any) ↦ (λ z (subst/c c_2 x any)))]
  [(subst/c (μ x c) x any) (μ x c)]
  [(subst/c (μ z c) x any) (μ z (subst/c c x any))]
  [(subst/c x x any) any]
  [(subst/c x z any) x]
  [(subst/c (any_l c ...) x any) (any_l (subst/c c x any) ...)])

;; flattens contract
(define-metafunction cpcf
  FC : c -> e
  [(FC (flat e)) e]
  [(FC (or/c c_1 c_2))
   (λ x (OR (e_1 x) (e_2 x)))
   (where e_1 (FC c_1))
   (where e_2 (FC c_2))
   (where x ,(variable-not-in (term (e_1 e_2)) (term X)))]
  [(FC (and/c c_1 c_2))
   (λ x (AND (e_1 x) (e_2 x)))
   (where e_1 (FC c_1))
   (where e_2 (FC c_2))
   (where x ,(variable-not-in (term (e_1 e_2)) (term X)))]
  [(FC (cons/c c_1 c_2))
   (λ x (AND/c (cons? x) (e_1 x) (e_2 x)))
   (where e_1 (FC c_1))
   (where e_2 (FC c_2))
   (where x ,(variable-not-in (term (e_1 e_2)) (term X)))]
  [(FC (μ x c)) (μ x (FC c))]
  [(FC x) x]
  [(FC (c_x ↦ (λ x c_y))) ,(error "flat!")])

;; macros
(define-metafunction cpcf
  AND : e ... -> e
  [(AND) #t]
  [(AND e) e]
  [(AND e_1 e ...) (if e_1 (AND e ...) #f)])
(define-metafunction cpcf
  OR : e ... -> e
  [(OR) #f]
  [(OR e) e]
  [(OR e_1 e ...)
   ((λ x (if x x e_rest)) e_1)
   (where e_rest (OR e ...))
   (where x ,(variable-not-in (term e_rest) (term tmp)))])

;; primitive ops
(define-metafunction cpcf
  δ : op V ... -> A
  [(δ int? n) #t]
  [(δ int? V) #f]
  [(δ false? #f) #t]
  [(δ false? V) #f]
  [(δ proc? op) #t]
  [(δ proc? ((λ x e) ρ)) #t]
  [(δ proc? (Arr D V)) #t]
  [(δ proc? V) #f]
  [(δ cons? (Cons V_1 V_2)) #t]
  [(δ cons? V) #f]
  [(δ add1 n) ,(+ 1 (term n))]
  [(δ car (Cons V_1 V_2)) V_1]
  [(δ cdr (Cons V_1 V_2)) V_2]
  [(δ cons V_1 V_2) (Cons V_1 V_2)]
  [(δ + m n) ,(+ (term m) (term n))]
  [(δ op V ...) blame])

(define-metafunction cpcf
  ev : e -> EA
  [(ev e)
   (A->EA A)
   (where (A) ,(judgment-holds (⇓ () e A) A))])
(define-metafunction cpcf
  A->EA : A -> EA
  [(A->EA (Cons V_1 V_2)) (Cons (A->EA V_1) (A->EA V_2))]
  [(A->EA V)
   function
   (where #t (δ proc? V))]
  [(A->EA A) A])

;; tests
(test-equal (term (ev 5)) 5)
(test-equal (term (ev +)) 'function)
(test-equal (term (ev (λ x e))) 'function)
(test-equal (term (ev ((λ x 4) 5))) 4)
(test-equal (term (ev ((λ x x) 5))) 5)
(test-equal (term (ev (if 0 1 2))) 1)
(test-equal (term (ev (if #f 1 2))) 2)
(test-equal (term (ev (add1 5))) 6)
(test-equal (term (ev (+ 5 6))) 11)
(test-equal (term (ev (int? 5))) #t)
(test-equal (term (ev (mon (flat int?) 5))) 5)
(test-equal (term (ev (mon (flat false?) 5))) 'blame)
(test-equal (term (ev (mon (or/c (flat false?) (flat int?)) 5))) 5)
(test-equal (term (ev (mon ((flat int?) ↦ (λ z (flat int?))) (λ x x)))) 'function)
(test-equal (term (ev ((mon ((flat int?) ↦ (λ z (flat int?))) (λ x x)) 1))) 1)
(test-equal (term (ev ((mon ((flat int?) ↦ (λ z (flat false?))) (λ x x)) 1))) 'blame)
(test-results)
