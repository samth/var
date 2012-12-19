#lang racket
(require redex)
(require "lang.rkt")

(provide ⇓ ⇓c ⇓a ⇓m)

(define-judgment-form scpcf
  #:mode     (⇓ I I I I I O   O O)
  #:contract (⇓ Γ ρ O ψ e Ans Γ o)
  
  [----- "val"
   (⇓ Γ ρ O ψ v (v (Γ-flush Γ ρ) O ψ) Γ ∅)]
  [----- "var"
   (⇓ Γ ρ O ψ x (Γ-refine (! ρ x) Γ (! O x)) Γ (! O x))]
  
  [(⇓ Γ ρ O ψ e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O ψ e_x V_x Γ_2 o_x)
   (⇓a Γ_2 V_f ([V_x o_x]) Ans Γ_3 o_y)
   ----- "app-1"
   (⇓ Γ ρ O ψ (e_f e_x) Ans Γ_3 o_y)]
  [(⇓ Γ ρ O ψ e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O ψ e_x V_x Γ_2 o_x)
   (⇓ Γ_2 ρ O ψ e_y V_y Γ_3 o_y)
   (⇓a Γ_3 V_f ([V_x o_x] [V_y o_y]) Ans Γ_4 o_z)
   ----- "app-2"
   (⇓ Γ ρ O ψ (e_f e_x e_y) Ans Γ_4 o_z)]
  [(⇓ Γ ρ O ψ e_f ERR Γ_1 o_f)
   ----- "app-err1"
   (⇓ Γ ρ O ψ (e_f e_x ...) ERR Γ_1 ∅)]
  [(⇓ Γ ρ O ψ e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O ψ e_x ERR Γ_2 o_x)
   ----- "app-err2"
   (⇓ Γ ρ O ψ (e_f e_x e_y ...) ERR Γ_2 ∅)]
  [(⇓ Γ ρ O ψ e_f V_f Γ_1 o_f)
   (⇓ Γ_1 ρ O ψ e_x V_x Γ_2 o_x)
   (⇓ Γ_2 ρ O ψ e_y ERR Γ_3 o_y)
   ----- "app-err3"
   (⇓ Γ ρ O ψ (e_f e_x e_y) ERR Γ_3 ∅)]
  
  [(⇓ Γ ρ O ψ e V Γ_1 o)
   (where (any ... ((#f ρ_t O_t ψ_t) Γ_2 o_t) any_1 ...) (δ false? (V o) Γ_1))
   (⇓ Γ_2 ρ O ψ e_1 Ans Γ_3 o_ans)
   ----- "if-true"
   (⇓ Γ ρ O ψ (if e e_1 e_2) Ans Γ_3 o_ans)]
  [(⇓ Γ ρ O ψ e V Γ_1 o)
   (where (any ... ((#t ρ_t O_t ψ_t) Γ_2 o_t) any_1 ...) (δ false? (V o) Γ_1))
   (⇓ Γ_2 ρ O ψ e_2 Ans Γ_3 o_ans)
   ----- "if-false"
   (⇓ Γ ρ O ψ (if e e_1 e_2) Ans Γ_3 o_ans)]
  [(⇓ Γ ρ O ψ e ERR Γ_1 o)
   ----- "if-err"
   (⇓ Γ ρ O ψ (if e e_1 e_2) ERR Γ_1 ∅)]
  
  [(⇓ Γ ρ O ψ (subst e x (μ (x) e)) Ans Γ_1 o)
   ----- "μ"
   (⇓ Γ ρ O ψ (μ (x) e) Ans Γ_1 o)]
  
  [(⇓c Γ ρ O ψ c D Γ_1)
   (⇓ Γ_1 ρ O ψ e V Γ_2 o)
   (⇓m Γ_2 D (V o) Ans Γ_3)
   ----- "mon"
   (⇓ Γ ρ O ψ (mon c e) Ans Γ_3 o)]
  [(⇓c Γ ρ O ψ c ERR Γ_1)
   ----- "mon-c-err"
   (⇓ Γ ρ O ψ (mon c e) ERR Γ_1 ∅)]
  [(⇓c Γ ρ O ψ c D Γ_1)
   (⇓ Γ_1 ρ O ψ e ERR Γ_2 o)
   ----- "mon-e-err"
   (⇓ Γ ρ O ψ (mon c e) ERR Γ_2 o)])

(define-judgment-form scpcf
  #:mode     (⇓c I I I I I O   O)
  #:contract (⇓c Γ ρ O ψ c Dns Γ)
  [(⇓ Γ ρ O ψ e V Γ_1 o)
   ----- "flat/c"
   (⇓c Γ ρ O ψ (flat e) (flat V) Γ_1)]
  [(⇓ Γ ρ O ψ e ERR Γ_1 o)
   ----- "flat/c-err"
   (⇓c Γ ρ O ψ (flat e) ERR Γ_1)]
  [----- "or/c"
   (⇓c Γ ρ O ψ (or/c c_1 c_2) (or/c c_1 c_2 (Γ-flush Γ ρ) O ψ) Γ)]
  [----- "and/c"
   (⇓c Γ ρ O ψ (and/c c_1 c_2) (and/c c_1 c_2 (Γ-flush Γ ρ) O ψ) Γ)]
  [----- "cons/c"
   (⇓c Γ ρ O ψ (cons/c c_1 c_2) (cons/c c_1 c_2 (Γ-flush Γ ρ) O ψ) Γ)]
  [----- "func/c"
   (⇓c Γ ρ O ψ (c_x ↦ (λ (x) c_y)) (c_x ↦ (λ (x) c_y) (Γ-flush Γ ρ) O ψ) Γ)]
  [(⇓c Γ ρ O (:: ψ [x ↦ ((μ (x) c) ρ O ψ)]) c Dns Γ_1)
   ----- "μ/c"
   (⇓c Γ ρ O ψ (μ (x) c) Dns Γ_1)]
  [(where (c ρ_c O_c ψ_c) (! ψ x))
   (⇓c (Γ-mk (dom ρ_c) Γ) ρ_c O_c ψ_c c Dns Γ_1)
   ----- "x/c"
   (⇓c Γ ρ O ψ x Dns (Γ-upd Γ Γ_1))])

(define-judgment-form scpcf
  #:mode     (⇓a I I I           O   O O)
  #:contract (⇓a Γ V ([V o] ...) Ans Γ o)
  
  [(⇓
    (Γ-reset (Γ-mk (dom ρ) Γ) x)
    (:: ρ [x ↦ V_x])
    (:: O [x ↦ (default-o o_x (del (dom ρ) x) [x])])
    ψ
    e
    Ans Γ_1 o_ans)
   ----- "app-λ"
   (⇓a Γ ((λ (x) e) ρ O ψ) ([V_x o_x])
       Ans (Γ-upd Γ (Γ-del Γ_1 x)) (default-o o_ans (del (dom Γ) x) ∅))]
  
  [(⇓m Γ (c_x ρ O ψ) (V_x o_x) V_x1 Γ_1)
   (⇓c
    (Γ-reset (Γ-mk (dom ρ) Γ_1) x)
    (:: ρ (x ↦ V_x1))
    (:: O (x ↦ (default-o o_x (del (dom ρ) x) [x])))
    ψ
    c_y
    D_y Γ_2)
   (⇓a (Γ-upd Γ_1 Γ_2) V_f ([V_x1 o_x]) V_y Γ_3 o_y)
   (⇓m Γ_3 D_y (V_y o_y) V_y1 Γ_4)
   ----- "app-arr"
   (⇓a Γ (arr (c_x ↦ (λ (x) c_y) ρ O ψ) V_f) ([V_x o_x]) V_y1 Γ_4 o_y)]
  
  [(where (any ... (Ans Γ_1 o) any_1 ...) (δ op (V_x o_x) ... Γ))
   ----- "app-prim"
   (⇓a Γ (op ρ_o O_o ψ_o) ([V_x o_x] ...) Ans Γ_1 o)])

(define-judgment-form scpcf
  #:mode     (⇓m I I  I     O   O)
  #:contract (⇓m Γ Cns (V o) Ans Γ)
  
  [(⇓a Γ V_p ([V o]) V_t Γ_1 o_t)
   (where (any ... ((#f ρ_t O_t ψ_t) Γ_2 o) any_1 ...) (δ false? (V_t o_t) Γ_1))
   ----- "flat-ok"
   (⇓m Γ (flat V_p) (V o) (flat-refine V V_p) Γ_2)]
  [(⇓a Γ V_p ([V o]) V_t Γ_1 o_t)
   (where (any ... ((#t ρ_t O_t ψ_t) Γ_2 o) any_1 ...) (δ false? (V_t o_t) Γ_1))
   ----- "flat-fail"
   (⇓m Γ (flat V_p) (V o) ERR Γ_2)]
  [(⇓a Γ V_p ([V o]) ERR Γ_1 o_t)
   ----- "flat-err"
   (⇓m Γ (flat V_p) (V o) ERR Γ_1)]
  
  [(where (any ... ((#t ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ proc? (V o) Γ))
   ----- "arr-ok"
   (⇓m Γ (c_x ↦ (λ (x) c_y) ρ O ψ) (V o) (arr (c_x ↦ (λ (x) c_y) ρ O ψ) V) Γ_t)]
  [(where (any ... ((#f ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ proc? (V o) Γ))
   ----- "arr-err"
   (⇓m Γ (c_x ↦ (λ (x) c_y) ρ O ψ) (V o) ERR Γ_t)]
  
  [(where #t (flat? c_1 ψ))
   (⇓m Γ (c_1 ρ O ψ) (V o) V_1 Γ_1)
   ----- "or/c-left"
   (⇓m Γ (or/c c_1 c_2 ρ O ψ) (V o) V_1 Γ_1)]
  [(where #t (flat? c_1 ψ))
   (⇓m Γ (c_1 ρ O ψ) (V o) ERR Γ_1)
   (⇓m Γ_1 (c_2 ρ O ψ) (V o) Ans Γ_2)
   ----- "or/c-right"
   (⇓m Γ (or/c c_1 c_2 ρ O ψ) (V o) Ans Γ_2)]
  [(where #f (flat? c_1 ψ))
   ----- "or/c-err"
   (⇓m Γ (or/c c_1 c_2 ρ O ψ) (V o) ERR Γ)]
  
  [(⇓m Γ (c_1 ρ O ψ) (V o) V_1 Γ_1)
   (⇓m Γ_1 (c_2 ρ O ψ) (V_1 o) Ans Γ_2)
   ----- "and/c"
   (⇓m Γ (and/c c_1 c_2 ρ O ψ) (V o) Ans Γ_2)]
  [(⇓m Γ (c_1 ρ O ψ) (V o) ERR Γ_1)
   ----- "and/c-err"
   (⇓m Γ (and/c c_1 c_2 ρ O ψ) (V o) ERR Γ_1)]
  
  [(where (any_1 ... ((#t ρ_t O_t ψ_t) Γ_1 o_t) any_2 ...) (δ cons? (V o) Γ))
   (where (any_3 ... (V_car Γ_2 o_car) any_4 ...) (δ car (V o) Γ_1))
   (⇓m Γ_2 (c_1 ρ O ψ) (V_car o_car) V_car1 Γ_3)
   (where (any_5 ... (V_cdr Γ_4 o_cdr) any_6 ...) (δ cdr (V o) Γ_3))
   (⇓m Γ_4 (c_2 ρ O ψ) (V_cdr o_cdr) V_cdr1 Γ_5)
   (where (any_7 ... (V_1 Γ_6 o_1) any_8 ...) (δ cons (V_car1 o_car) (V_cdr1 o_cdr) Γ_5))
   ----- "cons/c"
   (⇓m Γ (cons/c c_1 c_2 ρ O ψ) (V o) V_1 Γ_6)]
  [(where (any ... ((#f ρ_t O_t ψ_t) Γ_1 o_t) any_1 ...) (δ cons? (V o) Γ))
   ----- "cons/c-err1"
   (⇓m Γ (cons/c c_1 c_2 ρ O ψ) (V o) ERR Γ_1)]
  [(where (any_1 ... ((#t ρ_t O_t ψ_t) Γ_1 o_t) any_2 ...) (δ cons? (V o) Γ))
   (where (any_3 ... (V_car Γ_2 o_car) any_4 ...) (δ car (V o) Γ_1))
   (⇓m Γ_2 (c_1 ρ O ψ) (V_car o_car) ERR Γ_3)
   ----- "cons/c-err2"
   (⇓m Γ (cons/c c_1 c_2 ρ O ψ) (V o) ERR Γ_3)]
  [(where (any_1 ... ((#t ρ_t O_t ψ_t) Γ_1 o_t) any_2 ...) (δ cons? (V o) Γ))
   (where (any_3 ... (V_car Γ_2 o_car) any_4 ...) (δ car (V o) Γ_1))
   (⇓m Γ_2 (c_1 ρ O ψ) (V_car o_car) V_car1 Γ_3)
   (where (any_5 ... (V_cdr Γ_4 o_cdr) any_6 ...) (δ cdr (V o) Γ_3))
   (⇓m Γ_4 (c_2 ρ O ψ) (V_cdr o_cdr) ERR Γ_5)
   ----- "cons/c-err3"
   (⇓m Γ (cons/c c_1 c_2 ρ O ψ) (V o) ERR Γ_5)]
  
  [(⇓c (Γ-mk (dom ρ) Γ) ρ O ψ c D Γ_1)
   (⇓m (Γ-upd Γ Γ_1) D (V o) Ans Γ_2)
   ----- "closed-con"
   (⇓m Γ (c ρ O ψ) (V o) Ans Γ_2)]
  [(⇓c (Γ-mk (dom ρ) Γ) ρ O ψ c ERR Γ_1)
   ----- "closed-con-err"
   (⇓m Γ (c ρ O ψ) (V o) ERR Γ_1)])

(define-metafunction scpcf
  flat? : c ψ -> #t or #f
  [(flat? (c_x ↦ (λ (x) c_y)) ψ) #f]
  [(flat? (flat e) ψ) #t]
  [(flat? (any c_1 c_2) ψ) ,(and (term (flat? c_1 ψ)) (term (flat? c_2 ψ)))]
  [(flat? (μ (x) c) ψ) (flat? c ψ)]
  [(flat? x ψ) (flat? c)
               (where (c ρ O ψ) (! ψ x))])