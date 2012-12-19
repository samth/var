#lang racket
(require redex)
(require "lang.rkt")
(provide scpcf-m red)

;; extended language with machine state
(define-extended-language scpcf-m scpcf
  ; machine state
  [ς (C Γ o κ)
     (CC Γ κ)]
  ; kontinuation
  [κ mt
     (ap ([V o] ...) (C ...) κ)
     (if (C o) (C o) κ)
     (with-Γ Γ {x ...} κ)
     (flat-c κ)
     (mon-e (C o) κ)
     (mon-D D κ)
     (mon-C (c ρ O ψ) κ)
     (chk-or (V o) (or/c c c ρ O ψ) κ)
     (chk-cons (V o) (c ρ O ψ) κ)])

(define red
  (reduction-relation
   scpcf-m
   
   ;; on non-value (C Γ o κ)
   [--> ([x ρ O ψ] Γ o κ)
        ([Γ-refine (! ρ x) Γ (! O x)] Γ [! O x] κ)
        var]
   [--> ([(e_0 e_1 e_2 ...) ρ O ψ] Γ o κ)
        ([e_0 ρ O ψ] Γ ∅ [ap () ([e_1 ρ O ψ] [e_2 ρ O ψ] ...) κ])
        app-intro]
   [--> ([(if e e_1 e_2) ρ O ψ] Γ o κ)
        ([e ρ O ψ] Γ ∅ [if ([e_1 ρ O ψ] ∅) ([e_2 ρ O ψ] ∅) κ])
        if-intro]
   [--> ([(mon c e) ρ O ψ] Γ o κ)
        ([c ρ O ψ] Γ [mon-e ([e ρ O ψ] o) κ])
        mon-intro]
   [--> ([(μ (x) e) ρ O ψ] Γ o κ)
        ([(subst e x (μ (x) e)) ρ O ψ] Γ o κ)
        μ]
   
   ;; on non-contract (CC Γ κ)
   [--> ([(flat e) ρ O ψ] Γ κ)
        ([e ρ O ψ] Γ ∅ (flat-c κ))
        flat/c]
   [--> ([(or/c c_1 c_2) ρ O ψ] Γ κ)
        ([or/c c_1 c_2 ρ O ψ] Γ κ)
        or/c]
   [--> ([(and/c c_1 c_2) ρ O ψ] Γ κ)
        ([and/c c_1 c_2 ρ O ψ] Γ κ)
        and/c]
   [--> ([(cons/c c_1 c_2) ρ O ψ] Γ κ)
        ([cons/c c_1 c_2 ρ O ψ] Γ κ)
        cons/c]
   [--> ([(c_x ↦ (λ (x) c_y)) ρ O ψ] Γ κ)
        ([c_x ↦ (λ (x) c_y) ρ O ψ] Γ κ)
        func/c]
   [--> ([(μ (x) c) ρ O ψ] Γ κ)
        ([c ρ O (:: ψ [x ↦ ((μ (x) c) ρ O ψ)])] Γ κ)
        μ/c]
   [--> ([x ρ O ψ] Γ κ)
        ([c ρ_c O_c ψ_c] [Γ-mk (dom ρ_c) Γ] [WITH-Γ Γ {} κ])
        x/c
        (where (c ρ_c O_c ψ_c) (! ψ x))]
   
   ;; on evaluated contract (D Γ κ)
   [--> (D Γ [mon-e (C o) κ])
        (C Γ o [mon-D D κ])
        mon-swap]
   [--> (D Γ [with-Γ Γ_1 {x ...} κ])
        (D [Γ-upd Γ_1 (Γ-del Γ x ...)] κ)
        upd-Γ-1]
   
   ;; on value (V Γ o κ)
   [--> (V Γ o [if (C_1 o_1) (C_2 o_2) κ])
        (C_1 Γ_t o_1 κ)
        if-true
        (where (any ... ((#f ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ false? (V o) Γ))]
   [--> (V Γ o [if (C_1 o_1) (C_2 o_2) κ])
        (C_2 Γ_t o_2 κ)
        if-false
        (where (any ... ((#t ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ false? (V o) Γ))]
   [--> (V Γ o [flat-c κ])
        ([flat V] Γ κ)
        mk-flat]
   [--> (V Γ o [with-Γ Γ_1 {x ...} κ])
        (V [Γ-upd Γ_1 [Γ-del Γ x ...]] [default-o o (del (dom Γ) x ...) ∅] κ)
        upd-Γ-2]
   [--> (V Γ o [mon-D D κ])
        ς
        mon
        (where (any ... ς any_1 ...) ,(judgment-holds (MON D (V o) Γ κ ς) ς))]
   [--> (V Γ o [ap ([V_0 o_0] ...) (C_m C_m+1 ...) κ])
        (C_m Γ ∅ [ap ([V_0 o_0] ... [V o]) (C_m+1 ...) κ])
        app-swap]
   [--> (V Γ o [ap ([V_f o_f] [V_1 o_1] ...) () κ])
        ς
        app
        (where (any ... ς any_1 ...)
               ,(judgment-holds (APP V_f ([V_1 o_1] ... [V o]) Γ κ ς) ς))]
   [--> (V Γ o [chk-or (V_1 o_1) (or/c c_1 c_2 ρ O ψ) κ])
        (V_1′ Γ_t o_1 κ)
        or-left
        (where (any ... ((#f ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ false? (V o) Γ))
        (where (any ... V_1′ any_1 ...) (refine-v V_1 (c_1 ρ O ψ)))]
   [--> (V Γ o [chk-or (V_1 o_1) (c_2 ρ O ψ) κ])
        (V_1 Γ_t o_1 [mon-C (c_2 ρ O ψ) κ])
        or-right
        (where (any ... ((#f ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ false? (V o) Γ))]
   [--> (V Γ o [mon-C (c ρ O ψ) κ])
        ([c ρ O ψ] [Γ-mk (dom ρ) Γ] [WITH-Γ Γ {} (mon-e (V o) κ)])
        mon-C]
   [--> (V Γ o [chk-cons (V_1 o_1) (c ρ O ψ) κ])
        (V_1 Γ o_1 [ap ([(cdr [] [] []) ∅]) ()
                        (mon-C (c ρ O ψ) (ap ([(cons [] [] []) ∅] [V o]) [] κ))])
        chk-cons]))

(define-judgment-form scpcf-m
  #:mode     (MON I I     I I O)
  #:contract (MON D (V o) Γ κ (C Γ o κ))
  [-----
   (MON (flat V_p) (V o) Γ κ
        (V Γ o [ap ([V_p ∅]) () (if ((flat-refine V V_p) o) (ERR ∅) κ)]))]
  [-----
   (MON (or/c c_1 c_2 ρ O ψ) (V o) Γ κ
        ([(FC c_1) ρ O ψ] Γ ∅ [chk-ok (V o) (or/c c_1 c_2 ρ O ψ) κ]))]
  [-----
   (MON (and/c c_1 c_2 ρ O ψ) (V o) Γ κ
        (V Γ o [mon-C (c_1 ρ O ψ) (mon-C (c_2 ρ O ψ) κ)]))]
  [(where (any ... ((#f ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ cons? (V o) Γ))
   -----
   (MON (cons/c c_1 c_2 ρ O ψ) (V o) Γ κ
        (ERR Γ_t ∅ mt))]
  [(where (any ... ((#t ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ cons? (V o) Γ))
   -----
   (MON (cons/c c_1 c_2 ρ O ψ) (V o) Γ κ
        (V Γ_t o [ap ([(car [] [] []) ∅]) ()
                     (mon-C (c_1 ρ O ψ)
                            (chk-cons (V o) (c_2 ρ O ψ) κ))]))]
  [(where (any ... ((#f ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ proc? (V o) Γ))
   -----
   (MON (c_x ↦ (λ (x) c_y) ρ O ψ) (V o) Γ κ
        (ERR Γ_t ∅ mt))]
  [(where (any ... ((#t ρ_t O_t ψ_t) Γ_t o_t) any_1 ...) (δ proc? (V o) Γ))
   -----
   (MON (c_x ↦ (λ (x) c_y) ρ O ψ) (V o) Γ κ
        ([arr (c_x ↦ (λ (x) c_y) ρ O ψ) V] Γ o κ))])

(define-judgment-form scpcf-m
  #:mode     (APP I I           I I O)
  #:contract (APP V ([V o] ...) Γ κ (C Γ o κ))
  [----- "app-λ"
   (APP ((λ (x) e) ρ O ψ) ([V_x o_x]) Γ κ
        ([e (:: ρ [x ↦ V_x]) (:: O [x ↦ (default-o o_x (del (dom ρ) x) [x])]) ψ]
         [Γ-reset (Γ-mk (dom ρ) Γ) x]
         ∅
         [WITH-Γ Γ {x} κ]))]
  [(where (any ... V_x′ any_1 ...) (refine-v V_x (c_x ρ O ψ)))
   ----- "app-arr"
   (APP (arr (c_x ↦ (λ (x) c_y) ρ O ψ) V_f) ([V_x o_x]) Γ κ
        (V_x Γ o_x [mon-C (c_x ρ O ψ)
                          (ap ([V_f ∅]) ()
                              (mon-C
                               (c_y (:: ρ [x ↦ V_x′])
                                    (:: O [x ↦ (default-o o_x (del (dom ρ) x) [x])])
                                    ψ) κ))]))]
  [(where (any ... (Ans Γ_a o_a) any_1 ...) (δ op (V_i o_i) ... Γ))
   ----- "app-prim"
   (APP (op ρ O ψ) ([V_i o_i] ...) Γ κ (Ans Γ_a o_a κ))])
        

;; compacts adjacent with-Γ frames
(define-metafunction scpcf-m
  WITH-Γ : Γ {x ...} κ -> κ
  [(WITH-Γ Γ {x ...} (with-Γ Γ_1 {y ...} κ))
   (with-Γ [Γ-upd Γ_1 (Γ-del Γ y ...)] (∪ {x ...} {y ...}) κ)]
  [(WITH-Γ Γ {x ...} κ) (with-Γ Γ {x ...} κ)])

(define-metafunction scpcf-m
  ∪ : {any ...} {any ...} -> {any ...}
  [(∪ {any_1 ... any any_2 ...} {any_3 ... any_i any_4 ...})
   (∪ {any_1 ... any any_2 ...} {any_3 ... any_4 ...})]
  [(∪ {any_1 ...} {any_2 ...}) {any_1 ... any_2 ...}])

(define-metafunction scpcf-m
  load : e -> ς
  [(load e) ([e () () ()] [] ∅ mt)])

(define (try p)
  (traces red (term (load (desug ,p)))))


;;;; tests

#;(try (term ((λ (x)
              (if (int? x) (- 0 x)
                  (if (bool? x) (false? x) "ignore")))
            •)))

#;(try (term (let ([input •] [extra •])
             (if (and (or (int? input) (str? input))
                      (cons? extra))
                 (cond
                   [(and (int? input) (int? (car extra))) (+ input (car extra))]
                   [(int? (car extra)) (+ (str-len input) (car extra))]
                   [else 0])
                 "ignore"))))
