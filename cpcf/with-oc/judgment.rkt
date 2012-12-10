#lang racket
(require redex)
(require "lang.rkt")

(provide ⇓)

(define-judgment-form scpcf
  #:mode     (⇓ I I I I  O)
  #:contract (⇓ Γ ρ O e  A)
  [----- "val"
         (⇓ Γ ρ O v ([v (flush Γ ρ) O] Γ ∅))]
  [----- "var"
         (⇓ Γ ρ O x ([refine-with-Γ (! ρ x) Γ (! O x)] Γ [! O x]))]
  [(⇓ Γ ρ O e_f (((λ (x) e_y) ρ_f O_f) Γ_1 o_f))
   (⇓ Γ_1 ρ O e_x (V_x Γ_2 o_x))
   (⇓ [push (mk-Γ (dom ρ_f) Γ_2) x]
      [:: ρ_f (x ↦ V_x)]
      [:: O_f (x ↦ (default-o o_x (dom ρ_f) [x]))]
      e_y
      (V_y Γ_3 o_y))
   ----- "app-λ"
   (⇓ Γ ρ O (e_f e_x) (V_y [upd-Γ Γ_2 (pop Γ_3 x)] (default-o o_y (dom (pop Γ x)) ∅)))]
  [(⇓ Γ ρ O e_f (((• D ...) ρ_f O_f) Γ_1 o_f))
   (⇓ Γ_1 ρ O e_x (V_x Γ_2 o_x))
   (where (D_y ...) (D-ranges (D ...)))
   ----- "app-•-ok"
   (⇓ Γ ρ O (e_f e_x) (((• D_y ...) [] []) Γ_2 ∅))]
  [(⇓ Γ ρ O e_f (((• D ...) ρ_f O_f) Γ_1 o_f))
   (⇓ Γ_1 ρ O e_x (V_x Γ_2 o_x))
   ----- "app-•-err"
   (⇓ Γ ρ O (e_f e_x) ERR)]
  [(⇓ Γ ρ O e_f ((o1 ρ_f O_f) Γ_1 o_f))
   (⇓ Γ_1 ρ O e_x (V_x Γ_2 o_x))
   (where (any ... A any_1 ...) (δ o1 (V_x o_x) Γ_2))
   ----- "app-o1"
   (⇓ Γ ρ O (e_f e_x) A)]
  [(⇓ Γ ρ O e_f ((o2 ρ_f O_f) Γ_1 o_f))
   (⇓ Γ_1 ρ O e_x (V_x Γ_2 o_x))
   (⇓ Γ_2 ρ O e_y (V_y Γ_3 o_y))
   (where (any ... A any_1 ...) (δ o2 (V_x o_x) (V_y o_y) Γ_3))
   ----- "app-o2"
   (⇓ Γ ρ O (e_f e_x e_y) A)]
  [(⇓ Γ ρ O e_f ERR)
   -----"app-err1"
   (⇓ Γ ρ O (e_f e_x) ERR)]
  [(⇓ Γ ρ O e_f (V_f Γ_1 o_f))
   (⇓ Γ_1 ρ O e_x ERR)
   -----"app-err2"
   (⇓ Γ ρ O (e_f e_x e_y ...) ERR)]
  [(⇓ Γ ρ O e_f (V_f Γ_1 o_f))
   (⇓ Γ_1 ρ O e_x (V_x Γ_2 o_x))
   (⇓ Γ_2 ρ O e_y ERR)
   -----"app-err3"
   (⇓ Γ ρ O (e_f e_x e_y) ERR)]
  [(⇓ Γ ρ O e_f (((λ (x) e_y) ρ_f O_f) Γ_1 o_f))
   (⇓ Γ_1 ρ O e_x (V_x Γ_2 o_x))
   (⇓ [push (mk-Γ (dom ρ_f) Γ_2) x]
      [:: ρ_f (x ↦ V_x)]
      [:: O_f (x ↦ (default-o o_x (dom ρ_f) [x]))]
      e_y
      ERR)
   ----- "app-err4"
   (⇓ Γ ρ O (e_f e_x) ERR)]
  [(⇓ Γ ρ O e_0 (V_0 Γ_1 o_0))
   (where (any ... ((#f ρ_t O_t) Γ_t o_t) any_1 ...)
          (δ false? (V_0 o_0) Γ_1))
   (⇓ Γ_t ρ O e_1 A)
   ----- "if-true"
   (⇓ Γ ρ O (if e_0 e_1 e_2) A)]
  [(⇓ Γ ρ O e_0 (V_0 Γ_1 o_0))
   (where (any ... ((#t ρ_t O_t) Γ_t o_t) any_1 ...)
          (δ false? (V_0 o_0) Γ_1))
   (⇓ Γ_t ρ O e_2 A)
   ----- "if-false"
   (⇓ Γ ρ O (if e_0 e_1 e_2) A)]
  [(⇓ Γ ρ O e ERR)
   ----- "if-err"
   (⇓ Γ ρ O (if e e_1 e_2) ERR)]
  [(⇓ Γ ρ O (subst e x (μ (x) e)) A)
   ----- "μ"
   (⇓ Γ ρ O (μ (x) e) A)]
  [(where x (var-not-in e_p X))
   (⇓ Γ ρ O (let [x e] (if (e_p x) x blame)) A)
   ----- "mon-flat"
   (⇓ Γ ρ O (mon (flat e_p) e) A)]
  [(⇓ Γ ρ O (mon c_2 (mon c_1 e)) A)
   ----- "mon-and/c"
   (⇓ Γ ρ O (mon (and/c c_1 c_2) e) A)]
  [(where (e_p) (FC c_1))
   (where x (var-not-in e_p X))
   (⇓ Γ ρ O (let [x e] (if (e_p x) x (mon c_2 x))) A)
   ----- "mon-or/c"
   (⇓ Γ ρ O (mon (or/c c_1 c_2) e) A)]
  [(where x (var-not-in (c_1 c_2) X))
   (⇓ Γ ρ O (let [x (mon (flat cons?) e)]
              (cons (mon c_1 (car x)) (mon c_2 (cdr x))))
      A)
   ----- "mon-cons/c"
   (⇓ Γ ρ O (mon (cons/c c_1 c_2) e) A)]
  [(where f (var-not-in (c_x ↦ (λ (x) c_y)) F))
   (⇓ Γ ρ O (let [f e] (λ (x) (mon c_y (f (mon c_x x))))) A)
   ----- "mon-func/c"
   (⇓ Γ ρ O (mon (c_x ↦ (λ (x) c_y)) e) A)]
  [(⇓ Γ ρ O (mon (subst-c c x (μ (x) c)) e) A)
   ----- "mon-μ"
   (⇓ Γ ρ O (mon (μ (x) c) e) A)]
  
  ;; syntactic sugar
  [(⇓ Γ ρ O e A)
   -----
   (⇓ Γ ρ O (and e) A)]
  [(⇓ Γ ρ O (if e_1 (and e_2 e_3 ...) #f) A)
   -----
   (⇓ Γ ρ O (and e_1 e_2 e_3 ...) A)]
  [(⇓ Γ ρ O e A)
   -----
   (⇓ Γ ρ O (or e) A)]
  [(where x (var-not-in (e_2 e_3 ...) X))
   (⇓ Γ ρ O (let [x e_1] (if x x (or e_2 e_3 ...))) A)
   -----
   (⇓ Γ ρ O (or e_1 e_2 e_3 ...) A)]
  [(⇓ Γ ρ O ((λ (x) e) e_x) A)
   -----
   (⇓ Γ ρ O (let [x e_x] e) A)]
  [(⇓ Γ ρ O ((λ (x) e) e_x) A)
   -----
   (⇓ Γ ρ O (let ([x e_x]) e) A)]
  [(⇓ Γ ρ O (let [x e_x] (let ([y e_y] [z e_z] ...) e)) A)
   -----
   (⇓ Γ ρ O (let ([x e_x] [y e_y] [z e_z] ...) e) A)]
  [(⇓ Γ ρ O e A)
   -----
   (⇓ Γ ρ O (cond [else e]) A)]
  [(⇓ Γ ρ O (if e_1 e_2 (cond any ...)) A)
   -----
   (⇓ Γ ρ O (cond [e_1 e_2] any ...) A)]
  [(⇓ Γ ρ O e A)
   -----
   (⇓ Γ ρ O (begin e) A)]
  [(where x (var-not-in (e_2 e_3 ...) X))
   (⇓ Γ ρ O (let [x e_1] (begin e_2 e_3 ...)) A)
   -----
   (⇓ Γ ρ O (begin e_1 e_2 e_3 ...) A)]
  [-----
   (⇓ Γ ρ O • (((•) [] []) Γ ∅))])

;; tests
(judgment-holds
 (⇓ [] [] [] (let ([input •] [extra •])
               (if (and (or (int? input) (str? input))
                        (cons? extra))
                   (cond
                     [(and (int? input) (int? (car extra))) (+ input (car extra))]
                     [(int? (car extra)) (+ (str-len input) (car extra))]
                     [else 0])
                   "ignore"))
    ((0 ρ O) Γ o)))