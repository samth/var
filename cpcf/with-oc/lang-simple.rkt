#lang racket
(require redex)

(provide
 cpcf ⇓ subst subst-c FC var-not-in
 :: !)

(define-language cpcf
  ; expression
  [e v
     x
     (e e)
     (e e e)
     (if e e e)
     (mon c e)
     (μ (x) e)
     blame]
  [v (λ (x) e) b op]
  [b integer #t #f]
  [op o1 o2]
  [o1 p? add1 car cdr]
  [o2 + cons]
  [p? tt int? cons? false?]
  
  ; contract
  [c (flat e)
     (c ↦ (λ (x) c))
     (or/c c c)
     (and/c c c)
     (cons/c c c)
     (μ (x) c)]
  
  ; environment
  [ρ ([x ↦ V] ...)]
  
  ; closed value
  [V (v ρ) (Cons V V)]
  
  ; closed contract
  [D (c ρ)]
  
  ; evaluation answer
  [A ERR V]
  
  [(m n) integer]
  [(x y z) variable-not-otherwise-mentioned])

;; big-step semantics
(define-judgment-form cpcf
  #:mode (⇓ I I O)
  #:contract (⇓ ρ e A)
  [----- "val"
         (⇓ ρ v (v ρ))]
  [----- "var"
         (⇓ ρ x (! ρ x))]
  [(⇓ ρ e_f ((λ (x) e_y) ρ_f))
   (⇓ ρ e_x V_x)
   (⇓ (:: ρ_f [x ↦ V_x]) e_y A)
   ----- "app-λ"
   (⇓ ρ (e_f e_x) A)]
  [(⇓ ρ e_f (o1 ρ_o))
   (⇓ ρ e_x V_x)
   (where A (δ o1 V_x))
   ----- "app-o1"
   (⇓ ρ (e_f e_x) A)]
  [(⇓ ρ e_f (o2 ρ_o))
   (⇓ ρ e_1 V_1)
   (⇓ ρ e_2 V_2)
   (where A (δ o2 V_1 V_2))
   ----- "app-o2"
   (⇓ ρ (e_f e_1 e_2) A)]
  [(⇓ ρ e_i ERR)
   ----- "app-err"
   (⇓ ρ (e_1 ... e_i e_i+1 ...) ERR)]
  [(⇓ ρ e_0 V_t)
   (where (#f ρ_t) (δ false? V_t))
   (⇓ ρ e_1 A)
   ----- "if-true"
   (⇓ ρ (if e_0 e_1 e_2) A)]
  [(⇓ ρ e_0 (#f ρ_0))
   (⇓ ρ e_2 A)
   ----- "if-false"
   (⇓ ρ (if e_0 e_1 e_2) A)]
  [(⇓ ρ e ERR)
   ----- "if-err"
   (⇓ ρ (if e e_1 e_2) ERR)]
  [(⇓ ρ (subst e x (μ (x) e)) A)
   ----- "μ"
   (⇓ ρ (μ (x) e) A)]
  [(where x (var-not-in e_p X))
   (⇓ ρ ((λ (x) (if (e_p x) x blame)) e) A)
   ----- "mon-flat"
   (⇓ ρ (mon (flat e_p) e) A)]
  [(where f (var-not-in (c_x ↦ (λ (x) c_y)) f))
   (⇓ ρ ((λ (f) (λ (x) (mon c_y (f (mon c_x x))))) e) A)
   ----- "mon-func"
   (⇓ ρ (mon (c_x ↦ (λ (x) c_y)) e) A)]
  [(⇓ ρ (mon c_2 (mon c_1 e)) A)
   ----- "mon-and/c"
   (⇓ ρ (mon (and/c c_1 c_2) e) A)]
  [(where x (var-not-in (c_1 c_2) X))
   (where (e_p) (FC c_1))
   (⇓ ρ ((λ (x) (if (e_p x) x (mon c_2 x))) e) A)
   ----- "mon-or/c"
   (⇓ ρ (mon (or/c c_1 c_2) e) A)]
  [(where x (var-not-in (c_1 c_2) X))
   (⇓ ρ ((λ (x) (cons (mon c_1 (car x)) (mon c_2 (cdr x)))) (mon (flat cons?) e)) A)
   ----- "mon-cons/c"
   (⇓ ρ (mon (cons/c c_1 c_2) e) A)]
  [(⇓ ρ (mon (subst-c c x (μ (x) c)) e) A)
   ----- "mon-μ"
   (⇓ ρ (mon (μ (x) c) e) A)]
  [----- "blame"
   (⇓ ρ blame ERR)])

(define-metafunction cpcf
  δ : op V ... -> A
  [(δ int? (n ρ)) (#t [])]
  [(δ cons? (Cons V_1 V_2)) (#t [])]
  [(δ false? (#f ρ)) (#t [])]
  [(δ tt V) (#t [])]
  [(δ p? V) (#f [])]
  
  [(δ add1 (n ρ)) (,(add1 (term n)) [])]
  [(δ car (Cons V_1 V_2)) V_1]
  [(δ cdr (Cons V_1 V_2)) V_2]
  
  [(δ + (n ρ_1) (m ρ_2)) (,(+ (term n) (term m)) [])]
  [(δ cons V_1 V_2) (Cons V_1 V_2)]
  
  [(δ op V ...) ERR])

(define-metafunction cpcf
  var-not-in : any x -> x
  [(var-not-in any x) ,(variable-not-in (term e) (term x))])

(define-metafunction cpcf
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
(define-metafunction cpcf
  subst-c : c x any -> c
  [(subst-c (flat e) x any) (flat (subst e x any))]
  [(subst-c (c_1 ↦ (λ (x) c_2)) x any)
   ((subst-c c_1 x any) ↦ (λ (x) c_2))]
  [(subst-c (c_1 ↦ (λ (z) c_2)) x any)
   ((subst-c c_1 x any) ↦ (λ (z) (subst-c c_2 x any)))]
  [(subst-c (μ (x) c) x any) (μ (x) c)]
  [(subst-c (μ (z) c) x any) (μ (z) (subst-c c x any))]
  [(subst-c (any_l c ...) x any) (any_l (subst-c c x any) ...)])

;; flattens flat contract into expression, or #f for higher-order contracts
(define-metafunction cpcf
  FC : c -> (e) or #f
  [(FC (flat e)) (e)]
  [(FC (c ↦ any ...)) #f]
  [(FC (or/c c_1 c_2))
   ,(match (term ((FC c_1) (FC c_2)))
      [`((,e1) (,e2)) (let ([x (variable-not-in `(,e1 ,e2) 'x)])
                        (term [(λ (,x) (or [,e1 ,x] [,e2 ,x]))]))]
      [_ #f])]
  [(FC (and/c c_1 c_2))
   ,(match (term ((FC c_1) (FC c_2)))
      [`((,e1) (,e2)) (let ([x (variable-not-in `(,e1 ,e2) 'x)])
                        (term [(λ (,x) (and [,e1 ,x] [,e2 ,x]))]))]
      [_ #f])]
  [(FC (cons/c c_1 c_2))
   ,(match (term ((FC c_1) (FC c_2)))
      [`((,e1) (,e2)) (let ([x (variable-not-in `(,e1 ,e2) 'x)])
                        (term [(λ (,x)
                                 (and [cons? ,x] [,e1 (car ,x)] [,e2 (cdr ,x)]))]))]
      [_ #f])]
  [(FC (μ (x) c)) ,(match (term (FC c))
                     [`(,e) (term [(μ (x) ,e)])]
                     [#f #f])]
  [(FC x) (x)])


;; extends/updates environment
(define-metafunction cpcf
  :: : ([x ↦ any] ...) [x ↦ any] -> ([x ↦ any] ...)
  [(:: (any_1 ... [x ↦ any] any_2 ...) [x ↦ any_3])
   (any_1 ... [x ↦ any_3] any_2 ...)]
  [(:: (any ...) [x ↦ any_1]) ([x ↦ any_1] any ...)])

;; looks up environment at given key assumed exists
(define-metafunction cpcf
  ! : ([x ↦ any] ...) x -> any
  [(! (any_1 ... [x ↦ any] any_2 ...) x) any])

;; tests
(judgment-holds (⇓ [] 5 (5 ρ)))
(judgment-holds (⇓ [] + (+ ρ)))
(judgment-holds (⇓ [] (λ (x) 4) ((λ (x) 4) ρ)))
(judgment-holds (⇓ [] ((λ (x) 4) 5) (4 ρ)))
(judgment-holds (⇓ [] ((λ (x) x) 5) (5 ρ)))
(judgment-holds (⇓ [] (if 0 1 2) (1 ρ)))
(judgment-holds (⇓ [] (if #f 1 2) (2 ρ)))
(judgment-holds (⇓ [] (add1 5) (6 ρ)))
(judgment-holds (⇓ [] (+ 5 6) (11 ρ)))
(judgment-holds (⇓ [] (int? 5) (#t ρ)))
(judgment-holds (⇓ [] (mon (flat int?) 5) (5 ρ)))
(judgment-holds (⇓ [] (mon (flat false?) 5) ERR))
(judgment-holds (⇓ [] (mon (or/c (flat false?) (flat int?)) 5) (5 ρ)))
(judgment-holds (⇓ [] (mon ((flat int?) ↦ (λ (z) (flat int?))) (λ (x) x))
                   ((λ (x) e) ρ)))
(judgment-holds (⇓ [] (mon (flat tt) 7) (7 ρ)))
