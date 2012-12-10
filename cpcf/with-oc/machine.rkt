#lang racket
(require redex)
(require "lang.rkt")
(provide scpcf-m red)

;; extended language with machine state
(define-extended-language scpcf-m scpcf
  ; machine state
  [ς (C Γ o κ)]
  ; kontinuation
  [κ mt
     (@ ([V o] ...) (C ...) κ)
     (if C C κ)
     (with-Γ Γ x κ)])

(define red
  (reduction-relation
   scpcf-m
   
   ;; on non-value
   [--> ([blame ρ O] Γ o κ)
        ([blame [] []] [] ∅ mt)
        blame
        (side-condition (not (equal? (term κ) (term mt))))]
   [--> ([x ρ O] Γ o κ)
        ([refine-with-Γ (! ρ x) Γ (! O x)] Γ [! O x] κ)
        x]
   [--> ([(e_f e_1 e_2 ...) ρ O] Γ o κ)
        ([e_f ρ O] Γ ∅ [@ () ([e_1 ρ O] [e_2 ρ O] ...) κ])
        app-intro]
   [--> ([(if e e_1 e_2) ρ O] Γ o κ)
        ([e ρ O] Γ ∅ [if (e_1 ρ O) (e_2 ρ O) κ])
        if-intro]
   [--> ([(μ (x) e) ρ O] Γ o κ)
        ([(subst e x (μ (x) e)) ρ O] Γ o κ)
        μ]
   [--> ([(mon (flat e_p) e) ρ O] Γ o κ)
        ([(let [x e] (if (e_p x) x blame)) ρ O] Γ o κ)
        mon-flat
        (where x (var-not-in e_p X))]
   [--> ([(mon (and/c c_1 c_2) e) ρ O] Γ o κ)
        ([(mon c_2 (mon c_1 e)) ρ O] Γ o κ)
        mon-and/c]
   [--> ([(mon (or/c c_1 c_2) e) ρ O] Γ o κ)
        ([(let [x e] (if (e_p x) x (mon c_2 x))) ρ O] Γ o κ)
        mon-or/c
        (where (e_p) (FC c_1))
        (where x (var-not-in e_p X))]
   [--> ([(mon (cons/c c_1 c_2) e) ρ O] Γ o κ)
        ([(let [x (mon (flat cons?) e)]
            (cons (mon c_1 (car x)) (mon c_2 (cdr x)))) ρ O]
         Γ o κ)
        mon-cons/c
        (where x (var-not-in (c_1 c_2) X))]
   [--> ([(mon (μ (x) c) e) ρ O] Γ o κ)
        ([(mon (subst-c c x (μ (x) c)) e) ρ O] Γ o κ)
        mon-μ]
   [--> ([(mon (c_x ↦ (λ (x) c_y)) e) ρ O] Γ o κ)
        ([(let [f e] (λ (x) (mon c_y (f (mon c_x x))))) Γ o κ])
        mon-func/c
        (where f (var-not-in (c_x ↦ (λ (x) c_y)) F))]
   
   ;; on value
   [--> (V Γ o [if C_1 C_2 κ])
        (C_1 Γ_t ∅ κ)
        if-true
        (where (A ... ((#f ρ_t O_t) Γ_t o_t) A_1 ...) (δ false? (V o) Γ))]
   [--> (V Γ o [if C_1 C_2 κ])
        (C_2 Γ_t ∅ κ)
        if-false
        (where (A ... ((#t ρ_t O_t) Γ_t o_t) A_1 ...) (δ false? (V o) Γ))]
   [--> (V Γ o [@ (any ...) (C_m C_m+1 ...) κ])
        (C_m Γ ∅ [@ (any ... [V o]) (C_m+1 ...) κ])
        app-swap]
   [--> (V Γ o [@ ([(op ρ_o O_o) o_o] [V_x o_x] ...) () κ])
        (V_r Γ_1 o_r κ)
        δ
        (where (A ... (V_r Γ_1 o_r) A_1 ...) (δ op [V_x o_x] ... [V o] Γ))]
   [--> (V Γ o [@ ([(op ρ_o O_o) o_o] [V_x o_x] ...) () κ])
        ([blame () ()] [] ∅ mt)
        δ-err
        (where (A ... ERR A_1 ...) (δ op [V_x o_x] ... [V o] Γ))]
   [--> (V Γ o [@ ([((λ (x) e_y) ρ_f O_f) o_f]) () κ])
        ([e_y (:: ρ_f [x ↦ V]) (:: O_f [x ↦ (default-o o (dom ρ_f) [x])])]
         [push (mk-Γ (dom ρ_f) Γ) x]
         ∅
         [WITH-Γ Γ x κ])
        β]
   [--> (V Γ o [@ ([((• D ...) ρ_f O_f) o_f]) () κ])
        ([(• D_y ...) () ()] Γ ∅ κ)
        app-•-ok
        (where (D_y ...) (D-ranges (D ...)))]
   [--> (V Γ o [@ ([((• D ...) ρ_f O_f) o_f]) () κ])
        ([blame () ()] [] ∅ mt)
        app-•-err]
   [--> (V Γ o [with-Γ Γ_1 x κ])
        (V [upd-Γ Γ_1 (pop Γ x)] [default-o o (dom (pop Γ_1 x)) ∅] κ)
        upd-Γ]
   
   ;; syntactic sugar
   [--> ([(and e) ρ O] Γ o κ) ([e ρ O] Γ o κ) and-0]
   [--> ([(and e e_1 e_2 ...) ρ O] Γ o κ)
        ([(if e (and e_1 e_2 ...) #f) ρ O] Γ o κ)
        and+]
   [--> ([(or e) ρ O] Γ o κ) ([e ρ O] Γ o κ) or0]
   [--> ([(or e e_1 e_2 ...) ρ O] Γ o κ)
        ([(let [x e] (if x x (or e_1 e_2 ...))) ρ O] Γ o κ)
        or+
        (where x (var-not-in (e_1 e_2 ...) X))]
   [--> ([(let [x e_x] e) ρ O] Γ o κ)
        ([((λ (x) e) e_x) ρ O] Γ o κ)
        let0]
   [--> ([(let ([x e_x]) e) ρ O] Γ o κ)
        ([((λ (x) e) e_x) ρ O] Γ o κ)
        let*0]
   [--> ([(let ([x e_x] [y e_y] [z e_z] ...) e) ρ O] Γ o κ)
        ([((λ (x) (let ([y e_y] [z e_z] ...) e)) e_x) ρ O] Γ o κ)
        let*+]
   [--> ([(cond [else e]) ρ O] Γ o κ) ([e ρ O] Γ o κ) cond0]
   [--> ([(cond [e_1 e_2] any ...) ρ O] Γ o κ)
        ([(if e_1 e_2 (cond any ...)) ρ O] Γ o κ)
        cond+]
   [--> ([(begin e) ρ O] Γ o κ) ([e ρ O] Γ o κ)
        begin0]
   [--> ([(begin e e_1 e_2 ...) ρ O] Γ o κ)
        ([((λ (x) (begin e_1 e_2 ...)) e) ρ P] Γ o κ)
        begin+
        (where x (var-not-in (e_1 e_2 ...) X))]
   [--> ([• ρ O] Γ o κ) ([(•) () ()] Γ o κ) •]
   
   ))

;; compacts adjacent with-Γ frames
(define-metafunction scpcf-m
  WITH-Γ : Γ x κ -> κ
  [(WITH-Γ Γ x (with-Γ Γ_1 y κ)) (with-Γ [upd-Γ Γ_1 (pop Γ y)] x κ)]
  [(WITH-Γ Γ x κ) (with-Γ Γ x κ)])

(define-metafunction scpcf-m
  load : e -> ς
  [(load e) ([e () ()] [] ∅ mt)])

(define (try p)
  (traces red (term (load ,p))))


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
