#lang racket
(require redex)

;; Symbolic Core Racket
(define-language SCR
  ; program
  [(P Q) (M ... E)]
  ; module
  [(M N) (module f C V)]
  [(E F G) (f l)
           X
           A
           ((E E) l)
           (if E E E)
           (O E ...)
           (μ X E)
           (∨ E ...)
           (mon h f g C E) ; h,f,g: original, pos, neg
           ; syntactic sugar
           (∨ E ...)
           (∧ E ...)]
  ; prevalue
  [U n
     tt ff
     (λ X E)
     •
     (V V)
     empty]
  [(m n) natural]
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
      (mon f f f C CT)]
  ; for verifying contracts
  [Verified? Proved
             Refuted
             Unsure])


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
   
   ; primitive ops (non-deterministic)
   (E=> ((O V ...) l) V_1
        (where {V_0 ... V_1 V_2 ...} (δ l O V ...))
        δ)
   
   ; conditionals
   (E=> (if V E_t E_f) E_t
        (side-condition (member (term ff) (term (δ false? V))))
        if)
   (E=> (if V E_t E_f) E_f
        (side-condition (member (term tt) (term (δ false? V))))
        if-not)
   (E=> (∨ E ...) (desugar-∨ E ...)
        desugar-∨)
   (E=> (∧ E ...) (desugar-∧ E ...)
        desugar-∧)
   
   ; flat contract reduction
   (E=> (mon h f g C V) V ; TODO: paper appends C to V here, confirm?
        (side-condition (and (term (flat? C))
                             (equal? (term Proved) (term (verify V C)))))
        fc-proved)
   (E=> (mon h f g C V) (blame f h)
        (side-condition (and (term (flat? C))
                             (equal? (term Refuted) (term (verify V C)))))
        fc-refuted)
   (E=> (mon h f g C V) (if ((FC C) V) (refine V C) (blame f h))
        (side-condition (and (term (flat? C))
                             (equal? (term Unsure) (term (verify V C)))))
        fc-unsure)
   
   ; module reference
   (--> (M_1 ... (module f C V) M_2 ... (in-hole CT (f f)))
        V
        mod-ref-self)
   (--> (M_1 ... (module f C (U Cs)) M_2 ... (in-hole CT (f g)))
        (mon f f g C (U Cs))
        (side-condition (and (not (equal? (term f) (term g)))
                             (not (equal? (term •) (term U)))))
        mod-ref)
   (--> (M_1 ... (module F C (• Cs)) M_2 ... (in-hole CT (f g)))
        ; TODO: why have to refine (• Cs) with C with 'monitor' outside?
        (mon f f g C (refine (• Cs) C))
        (side-condition (not (equal? (term f) (term g))))
        mod-opaque)
   
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
  δ : l O V ... -> {A ...}
  
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
  
  ; =, assume this is like 'equal?', not just numbers?
  [(δ l = (U_1 Cs) (U_2 Ds))
   (to-bool ,(equal? (term V_1) (term V_2)))
   (side-condition (term (not (any-approx? U_1 U_2))))]
  [(δ l = V_1 V_2) {(promote tt) (promote ff)}]
  
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
  
  ; + (partial)
  [(δ l + (m Cs) (n Ds)) {(promote ,(+ (term m) (term n)))}]
  ; TODO: improve precision
  [(δ l + V_1 V_2) {(• ,nat/c) (blame l +)}])

;; converts contract to expression
(define-metafunction SCR
  FC : C -> E
  [(FC (μ X C)) (μ X (FC C))]
  [(FC X) X]
  [(FC (flat E)) E]
  [(FC (C ∧ D))
   (λ X (∧ ((FC C) X) ((FC D) X)))
   (where X ,(variable-not-in (term C D) (term x)))]
  [(FC (C ∨ D))
   (λ X (∨ ((FC C) X) ((FC D) X)))
   (where X ,(variable-not-in (term C D) (term x)))]
  [(FC (C D))
   (λ X (∧ (cons? X) ((FC C) (car X)) ((FC D) (cdr X))))
   (where X ,(variable-not-in (term C D) (term x)))])

;; capture-avoiding substitution
(define-metafunction SCR
  subst : any X E -> E
  [(subst X X E) E]
  [(subst Y X E) Y]
  [(subst ((λ X E) Cs) X F) ((λ X E) Cs)] ; var bound; ignore
  [(subst ((λ X E) Cs) Y F)
   (λ Z
     (subst (subst E X Z) Y F)) ; TODO: exponential blow-up risk
   (where Z ,(variable-not-in (term E Y F) (term X)))]
  [(subst ((E F) l) X G) ((subst E X G) (subst F X F) l)]
  [(subst (μ X E) X F) (μ X E)] ; var bound, ignore
  [(subst (μ X E) Y F)
   (λ Z
     (subst (subst E X Z) Y F)) ; TODO exponential blow-up risk
   (where Z ,(variable-not-in (term E Y F) (term X)))]
  [(subst (mon h f g C E) X F)
   (mon h f g (subst-con C X F) (subst E X F))]
  [(subst (any ...) X E) ((subst any X E) ...)]
  [(subst any X E) any])
(define-metafunction SCR
  subst-con : any X E -> C
  [(subst-con X X E) (flat E)]
  [(subst-con X Y E) X]
  [(subst-con (C ↦ (λ X D)) X E) (C ↦ (λ X D))] ; var bound, ignore
  [(subst-con (C ↦ (λ Y D)) X E)
   ((subst-con C X E)
    ↦ (λ Z
        (subst-con (subst-con D Y Z) X E))) ; TODO: exponential blow-up risk
   (where Z ,(variable-not-in (term C X E) (term Y)))]
  [(subst-con (flat E) X F) (flat (subst E X F))]
  [(subst-con (μ X C) X F) (μ X C)] ; var bound, ignore
  [(subst-con (μ X C) Y F)
   (μ Z
      (subst-con (subst-con C X Z) Y F)) ; TODO: exponential blow-up risk
   (where Z ,(variable-not-in (term C Y F) (term X)))]
  [(subst-con (any ...) X E) ((subst-con any X E) ...)]
  [(subst-con any X E) any])

;; (recursively) wraps prevalues with empty contract sets if not yet so
;; Allows writing SCR terms in a more readable form then wrapped with this
(define-metafunction SCR
  promote : any -> E
  [(promote (λ X any)) ((λ X (promote any)) {})]
  [(promote U) (U {})]
  [(promote A) A]
  [(promote (mon h f g C M))
   (mon h f g (promote-con C) (promote M))]
  [(promote (any ...)) ((promote any) ...)]
  [(promote any) any])
(define-metafunction SCR
  promote-con : any -> C
  [(promote-con (flat any)) (flat (promot any))]
  [(promote-con (C ↦ (λ X D)))
   ((promote-con C) ↦ (λ X (promote-con D)))]
  [(promote-con (any ...)) ((promote any) ...)]
  [(promote-con any) any])
  
;; converts and/or to if, supporting short-circuiting
(define-metafunction SCR
  desugar-∨ : E ... -> E
  [(desugar-∨) ff]
  [(desugar-∨ E) E] ; redundant, but reduce junks
  [(desugar-∨ E_0 E ...) (if E_0 tt (desugar-∨ E ...))])
(define-metafunction SCR
  desugar-∧ : E ... -> E
  [(desugar-∧) tt]
  [(desugar-∧ E) E] ; redundant, but reduce junks
  [(desugar-∧ E_0 E ...) (if E_0 (desugar-∧ E ...) ff)])