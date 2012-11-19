#lang racket
(require redex)
(require "lang.rkt")

(define-extended-language scpcf-m scpcf
  ; machine state
  [ς (C Γ o κ)]
  
  ; kontinuation
  [κ mt
     (@ ([V o] ...) (C ...) κ)
     (mon CC κ)
     (if C C κ)
     (with-Γ Γ {x ...} o κ)
     (with-V (V o) κ)])

(define red
  (reduction-relation
   scpcf-m
   
   ; distribute mon + if b/c i'll need this generalized later
   [--> ([(mon c e) ρ O] Γ o κ)
        ([mon (c ρ O) ((e ρ O) o)] Γ o κ)
        mon-distr]
   
   ; on non-values
   [--> ([x ρ O] Γ o κ)
        ([refine-with-Γ V Γ x] Γ [! O x] κ)
        var→val
        (where V (! ρ x))]
   [--> ([x ρ O] Γ o κ)
        ([(μ (z) e) ρ_μ O_μ] [mk-Γ (dom ρ_μ) Γ] ∅ [with-Γ Γ {} (! O x) κ])
        var→μ
        (where ((μ (z) e) ρ_μ O_μ) (! ρ x))]
   [--> ([(f e_1 e_2 ...) ρ O] Γ o κ)
        ([f ρ O] Γ ∅ [@ () ([e_1 ρ O] [e_2 ρ O] ...) κ])
        app-intro]
   [--> ([(if e e_1 ...) ρ O] Γ o κ)
        ([e ρ O] Γ ∅ [if (e_1 ρ O) ... κ])
        if-intro]
   [--> ([(μ (x) e) ρ O] Γ o κ)
        ([e (:: ρ [x ↦ ((μ (x) e) ρ O)]) (:: O [x ↦ x])]
         [push Γ x] ∅ [with-Γ Γ {x} ∅ κ])
        μ]
   [--> ([mon CC (C o_c)] Γ o κ)
        (C Γ o_c [mon CC κ]) ; TODO: is Γ appropriate? what rule generates this?
        mon-intro]
   
   ; on values
   [--> (V Γ o [@ ([V_0 o_0] ...) (C C_1 ...) κ])
        (C Γ ∅ [@ ([V_0 o_0] ... [V o]) (C_1 ...) κ])
        app-swap]
   [--> (V Γ o [@ [(((λ (x) e) ρ O) o_λ)] [] κ])
        ([e (:: ρ [x ↦ V]) (:: O [x ↦ (default-o (mb o (dom ρ)) x)])]
         [push (mk-Γ (dom ρ) Γ) x]
         ∅
         [with-Γ Γ {x} ∅ κ])
        app-λ]
   [--> (V_y Γ o_y [@ [((op ρ O) o_f) (V_x o_x) ...] [] κ])
        (V_z Γ_z o_z κ)
        app-op
        (where (any ... (V_z Γ_z o_z) any_1 ...)
               (δ op (V_x o_x) ... (V_y o_y) Γ))]
   [--> (V Γ o [@ [((mon ((c_1 ↦ (λ (x) c_2)) ρ O) (V_f o_f)) o_0)] [] κ])
        (V Γ o [mon (c_1 ρ O)
                    (@ ([V_f o_0]) []
                       (mon (c_2 ρ O) κ))])
        app-mon]
   [--> (V Γ o [if C_1 C_2 κ])
        (C_1 Γ ∅ κ)
        if-true
        (where (any ... ((#t ρ O) Γ_t o_t) any_1 ...)
               (δ true? (V o) Γ))]
   [--> (V Γ o [if C_1 C_2 κ])
        (C_2 Γ ∅ κ)
        if-false
        (where (any ... ((#f ρ O) Γ_t o_t) any_1 ...)
               (δ true? (V o) Γ))]
   [--> (V Γ o [mon (c ρ O) κ])
        ([e_p ρ O] Γ ∅ [@ () ([V o])
                          (if V_1 ERR κ)])
        mon-flat
        (where (e_p) (FC c))
        (where (any ... V_1 any_1 ...) (refine-v V (c ρ O)))]
   [--> (V Γ o [mon ((and/c c_1 c_2) ρ O) κ])
        (V Γ o [mon (c_1 ρ O) (mon (c_2 ρ O) κ)])
        mon-and/c
        (where #f (FC (and/c c_1 c_2)))]
   [--> (V Γ o [mon ((or/c c_1 c_2) ρ O) κ])
        ([e_p ρ O] Γ ∅ [@ () ([V o])
                          (if V_1 (mon (c_2 ρ O) (V o)) κ)])
        mon-or/c
        (where #f (FC c_2)) 
        (where (e_p) (FC c_1))
        (where (any ... V_1 any_1 ...) (refine-v V (c_1 ρ O)))]
   [--> (V Γ o [mon ((cons/c c_1 c_2) ρ O) κ])
        (V_1 Γ o-car [mon (c_1 ρ O)
                          (with-V (V_2 o-cdr)
                                  (mon (c_2 ρ O)
                                       (with-V ((V_1′ V_2′) o) κ)))])
        mon-cons/c
        (where #f (FC (cons/c c_1 c_2)))
        (where (any ... (V_1 V_2) any_1 ...) (split-cons (V o) Γ))
        (where o-car (acc-o car o))
        (where o-cdr (acc-o cdr o))
        (where (any_2 ... V_1′ any_3 ...) (refine-v V_1 (c_1 ρ O)))
        (where (any_4 ... V_2′ any_5 ...) (refine-v V_2 (c_2 ρ O)))]
   [--> (V Γ o [mon (x ρ O) κ])
        (V (mk-Γ (dom ρ_1) Γ) (mb o (dom ρ_1)) [mon (c ρ_1 O_1) κ])
        mon-x
        (where (c ρ_1 O_1) (! ρ x))]
   [--> (V Γ o [mon ((μ (x) c) ρ O) κ])
        (V [push Γ x] o [mon (c (:: ρ [x ↦ ((μ (x) c) ρ O)]) (:: O [x ↦ x])) κ])
        mon-μ]
   [--> (V Γ o [with-V (V_1 o_1) κ])
        (V_1 Γ o_1 κ)
        with-V]
   [--> (V Γ o [with-Γ Γ_1 {x} o_1 κ])
        (V [upd-Γ Γ_1 (pop Γ x)]
           [default-o′ (mb o_1 (dom Γ_1)) (mb o (dom Γ_1))]
           κ)
        with-Γ]
   [--> (V Γ o [with-Γ Γ_1 {} o_1 κ])
        (V [upd-Γ Γ_1]
           [default-o′ (mb o_1 (dom Γ_1)) (mb o (dom Γ_1))]
           κ)
        with-Γ′]
   
   ; on ERR
   [--> (ERR Γ o κ) (ERR [] ∅ mt)
        err]))

(define-metafunction scpcf-m
  default-o′ : o o -> o
  [(default-o′ ∅ o) o]
  [(default-o′ o′ o) o′])


;;;; tests ; TODO more!!

#;(traces red
          (term ([((λ (x)
                     (if (int? x) (- 0 x)
                         (if (bool? x) (false? x) "ignore")))
                   (•)) () ()] () ∅ mt)))
