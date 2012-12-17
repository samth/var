#lang racket
(require redex)

(provide
 cpcf ⇓ ⇓c subst subst-c #;FC var-not-in
 :: !)

(define-language cpcf
  ; expression
  [e v
     x
     (e e e ...)
     (if e e e)
     (mon c e)
     (μ (x) e)]
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
     (μ (x) c)
     x]
  
  ; environment
  [ρ ([x ↦ V] ...)]
  [ψ ([x ↦ (c ρ ψ)] ...)]
  
  ; closed value
  [V (v ρ ψ) (Cons V V) (arr D V)]
  
  [D (flat V)
     (c ↦ (λ (x) c) ρ ψ)
     (or/c c c ρ ψ)
     (and/c c c ρ ψ)
     (cons/c c c ρ ψ)]
  
  ; evaluation answer
  [Ans ERR V]
  [Dns ERR D]
  [CC (c ρ ψ) Dns]
  
  [(m n) integer]
  [(x y z) variable-not-otherwise-mentioned])

;; big-step semantics
(define-judgment-form cpcf
  #:mode     (⇓ I I I O)
  #:contract (⇓ ρ ψ e Ans)
  [----- "val"
   (⇓ ρ ψ v (v ρ ψ))]
  [----- "var"
   (⇓ ρ ψ x (! ρ x))]
  [(⇓ ρ ψ e_f V_f)
   (⇓ ρ ψ e_x V_x) ...
   ----- "app"
   (⇓ ρ ψ (e_f e_x ...) (APP V_f V_x ...))]
  [(⇓ ρ ψ e_1 V_1) ...
   (⇓ ρ ψ e_i ERR)
   ----- "app-err"
   (⇓ ρ ψ (e_1 ... e_i e_i+1 ...) ERR)]
  [(⇓ ρ ψ e V_t)
   (where (#f ρ_t ψ_t) (δ false? V_t))
   (⇓ ρ ψ e_1 Ans)
   ----- "if-true"
   (⇓ ρ ψ (if e e_1 e_2) Ans)]
  [(⇓ ρ ψ e V_t)
   (where (#t ρ_t ψ_t) (δ false? V_t))
   (⇓ ρ ψ e_2 Ans)
   ----- "if-false"
   (⇓ ρ ψ (if e e_1 e_2) Ans)]
  [(⇓ ρ ψ e ERR)
   ----- "if-err"
   (⇓ ρ ψ (if e e_1 e_2) ERR)]
  [(⇓ ρ ψ (subst e x (μ (x) e)) Ans)
   ----- "μ"
   (⇓ ρ ψ (μ (x) e) Ans)]
  [(⇓c ρ ψ c D)
   (⇓ ρ ψ e V)
   ----- "mon"
   (⇓ ρ ψ (mon c e) (MON D V))]
  [(⇓c ρ ψ c ERR)
   ----- "mon-c-err"
   (⇓ ρ ψ (mon c e) ERR)]
  [(⇓c ρ ψ c D)
   (⇓ ρ ψ e ERR)
   ----- "mon-e-err"
   (⇓ ρ ψ (mon c e) ERR)])
  
(define-judgment-form cpcf
  #:mode     (⇓c I I I O)
  #:contract (⇓c ρ ψ c Dns)
  [(⇓ ρ ψ e V)
   ----- "flat"
   (⇓c ρ ψ (flat e) (flat V))]
  [(⇓ ρ ψ e ERR)
   ----- "flat-err"
   (⇓c ρ ψ (flat e) ERR)]
  [----- "or/c"
   (⇓c ρ ψ (or/c c_1 c_2) (or/c c_1 c_2 ρ ψ))]
  [----- "and/c"
   (⇓c ρ ψ (and/c c_1 c_2) (and/c c_1 c_2 ρ ψ))]
  [----- "cons/c"
   (⇓c ρ ψ (cons/c c_1 c_2) (cons/c c_1 c_2 ρ ψ))]
  [----- "func/c"
   (⇓c ρ ψ (c_x ↦ (λ (x) c_y)) (c_x ↦ (λ (x) c_y) ρ ψ))]
  [(⇓c ρ [:: ψ (x ↦ ((μ (x) c) ρ ψ))] c Dns)
   ----- "μ/c"
   (⇓c ρ ψ (μ (x) c) Dns)]
  [(where (c ρ_1 ψ_1) (! ψ x))
   (⇓c ρ_1 ψ_1 c Dns)
   ----- "x/c"
   (⇓c ρ ψ x Dns)])

(define-metafunction cpcf
  APP : V V ... -> Ans
  [(APP [(λ (x) e) ρ ψ] V)
   Ans
   (where (Ans) ,(judgment-holds (⇓ [:: ρ (x ↦ V)] ψ e Ans) Ans))]
  [(APP [arr (c_x ↦ (λ (x) c_y) ρ ψ) V_f] V_x)
   (MON [c_y (:: ρ [x ↦ V]) ψ]
        (APP V_f
             (MON [c_x ρ ψ] V_x)))]
  [(APP [op ρ_o ψ_o] V ...) (δ op V ...)])

(define-metafunction cpcf
  MON : CC Ans -> Ans
  [(MON (flat V_p) V)
   ERR
   (where (#t ρ_t ψ_t) (δ false? (APP V_p V)))]
  [(MON (flat V_p) V)
   V
   (where (#f ρ_t ψ_t) (δ false? (APP V_p V)))]
  [(MON (c_x ↦ (λ (x) c_y) ρ ψ) V) (arr (c_x ↦ (λ (x) c_y) ρ ψ) V)]
  [(MON (or/c c_1 c_2 ρ ψ) V)
   V
   (where #t (FC c_1 ρ ψ V))]
  [(MON (or/c c_1 c_2 ρ ψ) V)
   (MON (c_2 ρ ψ) V)
   (where #f (FC c_1 ρ ψ V))]
  [(MON (and/c c_1 c_2 ρ ψ) V) (MON (c_2 ρ ψ) (MON (c_1 ρ ψ) V))]
  [(MON (cons/c c_1 c_2 ρ ψ) V)
   V
   (where (#t ρ_t ψ_t) (δ cons? V))
   (where (V_1) (MON (c_1 ρ ψ) (δ car V)))
   (where (V_2) (MON (c_2 ρ ψ) (δ cdr V)))]
  [(MON (c ρ ψ) V)
   (MON D V)
   (where (D) ,(judgment-holds (⇓c ρ ψ c D) D))]
  [(MON CC ERR) ERR]
  [(MON ERR Ans) ERR])

(define-metafunction cpcf
  FC : c ρ ψ V -> #t or #f or ERR
  [(FC (flat e_p) ρ ψ V)
   #f
   (where (V_p) ,(judgment-holds (⇓ ρ ψ e_p V_p) V_p))
   (where (#f ρ_t ψ_t) (APP V_p V))]
  [(FC (flat e_p) ρ ψ V)
   #t
   (where (V_p) ,(judgment-holds (⇓ ρ ψ e_p V_p) V_p))
   (where V_t (APP V_p V))]
  [(FC (or/c c_1 c_2) ρ ψ V) (OR (FC c_1 ρ ψ V) (FC c_2 ρ ψ V))]
  [(FC (and/c c_1 c_2) ρ ψ V) (AND (FC c_1 ρ ψ V) (FC c_2 ρ ψ V))]
  [(FC (cons/c c_1 c_2) ρ ψ V)
   (AND (δ cons? V) (FC c_1 ρ ψ (δ car V)) (FC c_2 ρ ψ (δ cdr V)))]
  [(FC (μ (x) c) ρ ψ V) (FC (subst-c c x (μ (x) c)) ρ ψ V)]
  [(FC x ρ ψ V)
   (FC c ρ_1 ψ_1 V)
   (where (c ρ_1 ψ_1) (! ψ_1 x))]
  ; catch-all clause for higher-order contract and APP failure
  [(FC c ρ ψ V) ERR])

(define-metafunction cpcf
  OR : any ... -> any
  [(OR) #f]
  [(OR ERR any ...) ERR]
  [(OR #f any ...) (OR any ...)]
  [(OR (#f ρ ψ) any ...) (OR any ...)]
  [(OR any ...) #t])
(define-metafunction cpcf
  AND : any ... -> any
  [(AND) #t]
  [(AND ERR any ...) ERR]
  [(AND #t any ...) (AND any ...)]
  [(AND (#t ρ ψ) any ...) (AND any ...)]
  [(AND any ...) #f])
   
              
(define-metafunction cpcf
  δ : op V ... -> Ans
  [(δ int? (n ρ ψ)) (#t [] [])]
  [(δ cons? (Cons V_1 V_2)) (#t [] [])]
  [(δ false? (#f ρ ψ)) (#t [] [])]
  [(δ tt V) (#t [] [])]
  [(δ p? V) (#f [] [])]
  
  [(δ add1 (n ρ ψ)) (,(add1 (term n)) [] [])]
  [(δ car (Cons V_1 V_2)) V_1]
  [(δ cdr (Cons V_1 V_2)) V_2]
  
  [(δ + (n ρ_1 ψ) (m ρ_2 ψ)) (,(+ (term n) (term m)) [] [])]
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
  [(subst v x any) v])
(define-metafunction cpcf
  subst-c : c x any -> c
  [(subst-c (flat e) x any) (flat (subst e x any))]
  [(subst-c x x any) any]
  [(subst-c x z any) x]
  [(subst-c (c_1 ↦ (λ (x) c_2)) x any)
   ((subst-c c_1 x any) ↦ (λ (x) c_2))]
  [(subst-c (c_1 ↦ (λ (z) c_2)) x any)
   ((subst-c c_1 x any) ↦ (λ (z) (subst-c c_2 x any)))]
  [(subst-c (μ (x) c) x any) (μ (x) c)]
  [(subst-c (μ (z) c) x any) (μ (z) (subst-c c x any))]
  [(subst-c (any_l c ...) x any) (any_l (subst-c c x any) ...)])

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
(judgment-holds (⇓ [] [] 5 (5 ρ ψ)))
(judgment-holds (⇓ [] [] + (+ ρ ψ)))
(judgment-holds (⇓ [] [] (λ (x) 4) ((λ (x) 4) ρ ψ)))
(judgment-holds (⇓ [] [] ((λ (x) 4) 5) (4 ρ ψ)))
(judgment-holds (⇓ [] [] ((λ (x) x) 5) (5 ρ ψ)))
(judgment-holds (⇓ [] [] (if 0 1 2) (1 ρ ψ)))
(judgment-holds (⇓ [] [] (if #f 1 2) (2 ρ ψ)))
(judgment-holds (⇓ [] [] (add1 5) (6 ρ ψ)))
(judgment-holds (⇓ [] [] (+ 5 6) (11 ρ ψ)))
(judgment-holds (⇓ [] [] (int? 5) (#t ρ ψ)))
(judgment-holds (⇓ [] [] (mon (flat int?) 5) (5 ρ ψ)))
(judgment-holds (⇓ [] [] (mon (flat false?) 5) ERR))
(judgment-holds (⇓ [] [] (mon (or/c (flat false?) (flat int?)) 5) (5 ρ ψ)))
(judgment-holds (⇓ [] [] (mon ((flat int?) ↦ (λ (z) (flat int?))) (λ (x) x))
                   (arr D V)))
(judgment-holds (⇓ [] [] (mon (flat tt) 7) (7 ρ ψ)))
