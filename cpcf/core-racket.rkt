#lang racket
(require redex)

;; Symbolic Core Racket
(define-language SCR
  ; program
  [(P Q) (M ... E)]
  ; module
  [(M N) (module f C V)]
  [E (f l)
     X
     A
     ((E E) l)
     (if E E E)
     (O E ...)
     (μ X E)
     (mon h f g C E)] ; h,f,g: original, pos, neg
  ; prevalue
  [U n
     tt ff
     (λ X E)
     •
     (V V)
     empty]
  [n integer]
  ; value
  [V (U Cs)]
  ; contract
  [(C D) X
         (C ↦ (λ X C))
         (flat E)
         (C C)
         (C ∨ C)
         (C ∧ C)
         (μ X C)]
  [(Cs Ds) (C ...)]
  ; primitive ops
  [O add1 car cdr cons + = o?]
  [o? nat? bool? empty? cons? proc? false?]
  ; answer
  [A V
     (blame l_1 l_2)] ; l_1 breaks contract with l_2
  [(X Y Z f g h l) variable-not-otherwise-mentioned]
  
  ; eval context for expressions
  [CT hole
      ((CT E) l)
      ((V CT) l)
      (if CT E E)
      (O V ... CT E ...)
      (mon f f f C CT)])


;; reduction semantics
(define SCR-red
  (reduction-relation
   SCR
   ; function application
   (E=> (((λ X E) V) l) (subst E X V)
        β)
   (E=> ((V_f V_x) l) (blame l Λ)
        (side-condition (member (term ff)
                                (term (δ proc? V_f))))
        β-err)
   
   ; primitive ops
   ; TODO: how to expression non-determinism with arbitrary number of branches?
   (E=> ((O V ...) l) V_0
        (where {V_0} (δ l O V ...))
        δ0)
   (E=> ((O V ...) l) V_1
        (where {V_1 V_2} (δ l O V ...))
        δ1)
   (E=> ((O V ...) l) V_2
        (where {V_1 V_2} (δ l O V ...))
        δ2)
   
   ; conditionals
   (E=> (if V E_t E_f) E_t
        (side-condition (member (term ff) (term (δ false? V))))
        if)
   (E=> (if V E_t E_f) E_f
        (side-condition (member (term tt) (term (δ false? V))))
        if-not)
   
   ; blame propagation
   (--> (M ... (in-hole CT (blame f g))) (M ... (blame f g))
        (side-condition (not (equal? (term CT) (term hole))))
        blame-prop)
   with
   [(--> (M ... (in-hole CT E_1)) (N ... (in-hole CT E_2)))
    (E=> E_1 E_2)]))

(define nat/c (term (flat (promote (λ X (nat? X))))))
(define bool/c (term (flat (promote (λ X (bool? X))))))

;; interprets primitive operations
(define-metafunction SCR
  ; restrict range to make sure i don't accidentally make this go out of sync
  ; with above reduction rules
  δ : l O V ... -> {A} or {A A}
  
  ; predicates
  [(δ l proc? ((λ X E) Cs)) {(promote tt)}]
  [(δ l nat? (n Cs)) {(promote tt)}]
  [(δ l cons? (((V_l Cs) (V_r Ds)) Cs_p)) {(promote tt)}]
  [(δ l empty? (empty Cs)) {(promote tt)}]
  [(δ l bool? (b Cs)) {(promote tt)}]
  [(δ l false? ff) {(promote tt)}]
  ; TODO: consider opaque value being able to satisfy contracts
  [(δ l o? (• Cs) ...) {(promote tt) (promote ff)}]
  [(δ l o? E) {(promote ff)}]
  
  ; add1 (partial)
  [(δ l add1 (n Cs)) {(promote ,(add1 (term n)))}]
  [(δ l add1 (• Cs))
   {(• {,nat/c})}
   (side-condition (term (can-prove? (• Cs) ,nat/c)))]
  [(δ l add1 (• Cs)) {(• {,nat/c}) (blame l add1)}]
  [(δ l add1 V) {(blame l add1)}]
  
  ; car (partial)
  [(δ l car ((V_1 V_2) Cs)) {V_1}]
  [(δ l car (• Cs))
   {(• {,cons/c})}
   (side-condition (equal? (term (verify (• Cs) ,cons/c)) (term Proved)))]
  [(δ l car (• Cs))
   {(• {,cons/c}) (blame l car)}
   (side-condition (equal? (term (verify (• Cs) ,cons/c)) (term Unsure)))]
  [(δ l car V) {(blame l car)}]
  
  ; cdr (partial)
  [(δ l cdr ((V_1 V_2) Cs)) {V_2}]
  [(δ l cdr (• Cs))
   {(• {,cons/c})}
   (side-condition (equal? (term (verify (• Cs) ,cons/c)) (term Proved)))]
  [(δ l cdr (• Cs))
   {(• {,cons/c}) (blame l cdr)}
   (side-condition (equal? (term (verify (• Cs) ,cons/c)) (term Unsure)))]
  [(δ l cdr V) {(blame l cdr)}]
  
  ; cons
  [(δ l cons V_1 V_2) {(promote (V_1 V_2))}]
  
  ; =, assume this is like 'equal?', not just numbers?
  [(δ l = (U_1 Cs) (U_2 Ds))
   (to-bool ,(equal? (term V_1) (term V_2)))
   (side-condition (term (not (any-approx? U_1 U_2))))]
  [(δ l = V_1 V_2) {(promote tt) (promote ff)}])
  
  
  