#lang racket
(require redex)

;; Symbolic Core Racket
(define-language SCR
  ; program
  [(P Q) (M ... E)]
  ; module
  [(M N) (module f C V)]
  [(E F G) (f l) ; module reference
           X
           A
           (E E l) ; function application with label
           (if E E E)
           (O E ... l) ; primitive application
           (μ X E)
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
      (CT E l)
      (V CT l)
      (if CT E E)
      (O V ... CT E ... l)
      (mon f f f C CT)]
  ; result for verifying contracts
  [Verified? Proved
             Refuted
             Unsure])


;; reduction semantics
(define SCR-red
  (reduction-relation
   SCR
   ; function application
   (E=> ((λ X E) V l) (subst E X V)
        β)
   (E=> (V_f V_x l) (blame l Λ)
        (side-condition (member (term (promote ff))
                                (term (δ † proc? V_f))))
        β-err)
   (E=> ((• Cs) V l)
        (• ,{map (λ (c) (term (subst-range-con ,c V)))
                 (filter (λ (c) (term (higher-order? ,c)))
                         (term Cs))})
        (side-condition (member (term (promote tt))
                                (term (δ † proc? (• Cs)))))
        β-opaque)
   (E=> ((• Cs) V l) (,havoc V)
        (side-condition (member (term (promote tt))
                                (term (δ † proc? (• Cs)))))
        β-opaque-havoc)
   
   ; primitive ops (non-deterministic)
   (E=> (O V ... l) V_1
        (where {V_0 ... V_1 V_2 ...} (δ l O V ...))
        δ)
   
   ; conditionals
   (E=> (if V E_t E_f) E_t
        (side-condition (member (term ff) (term (δ † false? V))))
        if)
   (E=> (if V E_t E_f) E_f
        (side-condition (member (term tt) (term (δ † false? V))))
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
   
   ; function contract reduction
   (E=> (mon h f g (C ↦ (λ X D)) V)
        ((λ X (mon h f g D (V (mon h g f C X)))) {})
        (side-condition (member (term (promote tt))
                                (term (δ † proc? V))))
        con-fun)
   (E=> (mon h f g (C ↦ (λ X D)) V)
        (blame f h)
        (side-condition (member (term (promote ff))
                                (term (δ † proc? V))))
        con-fun-not-proc)
   
   ; other higher-order contract reductions
   (E=> (mon h f g (C D) V)
        (((mon h f g C (car V_p)) (cons h f g D (cdr V_p))) {})
        (where V_p (refine V ,cons/c))
        (side-condition
         (and (term (higher-order? (C D)))
              (member (term (promote tt)) (term (δ † cons? V)))))
        ho-con)
   (E=> (mon h f g (C D) V) (blame f h)
        (side-condition
         (and (term (higher-order? (C D)))
              (member (term (promote ff)) (term (δ † cons? V)))))
        ho-con-err)
   (E=> (mon h f g (μ X C) V)
        (mon h f g (subst-con C X (μ X C)) V) ; rely on productivity
        (side-condition (term (higher-order? (μ X C))))
        ho-con-μ)
   (E=> (mon h f g (C ∧ D) V)
        (mon h f g D (mon h f g C V))
        (side-condition (term (higher-order? (C ∧ D))))
        ho-con-∧)
   (E=> (mon h f g (C ∨ D) V)
        (if ((F C) V) (refine V C) (mon h f g D V))
        (side-condition (and (term (higher-order? (C ∨ D)))
                             (equal? (term Unsure) (term (verify V C)))))
        ho-con-∨-unsure)
   (E=> (mon h f g (C ∨ D) V) V
        (side-condition (and (term (higher-order? (C ∨ D)))
                             (equal? (term Proved) (term (verify V C)))))
        ho-con-∨-proved)
   (E=> (mon h f g (C ∨ D) V) (mon D V)
        (side-condition (and (term (higher-order? (C ∨ D)))
                             (equal? (term Refuted) (term (Verify V C)))))
        ho-con-∨-refuted)
   
   ; module reference
   (--> (M_1 ... (module f C V) M_2 ... (in-hole CT (f f)))
        (M_1 ... (module f C V) M_2 ... (in-hole CT V))
        mod-ref-self)
   (--> (M_1 ... (module f C (U Cs)) M_2 ... (in-hole CT (f g)))
        (M_1 ... (module f c (U Cs)) M_2 ...
             (in-hole CT (mon f f g C (U Cs))))
        (side-condition (and (not (equal? (term f) (term g)))
                             (not (equal? (term •) (term U)))))
        mod-ref)
   (--> (M_1 ... (module F C (• Cs)) M_2 ... (in-hole CT (f g)))
        ; TODO: why have to refine (• Cs) with C with 'monitor' outside?
        (M_1 ... (module F C (• Cs)) M_2 ...
             (in-hole CT (mon f f g C (refine (• Cs) C))))
        (side-condition (not (equal? (term f) (term g))))
        mod-opaque)
   
   ; blame propagation
   (--> (M ... (in-hole CT (blame f g))) (M ... (blame f g))
        (side-condition (not (equal? (term CT) (term hole))))
        blame-prop)
   with
   [(--> (M ... (in-hole CT E_1)) (M ... (in-hole CT E_2)))
    (E=> E_1 E_2)]))

;; interprets primitive operations
(define-metafunction SCR
  δ : l O V ... -> {A ...}
  
  ;; predicates (total)
  ; concrete values that satisfy predicates
  [(δ l proc? ((λ X E) Cs)) {(promote tt)}]
  [(δ l nat? (n Cs)) {(promote tt)}]
  [(δ l cons? (((V_l Cs) (V_r Ds)) Cs_p)) {(promote tt)}]
  [(δ l empty? (empty Cs)) {(promote tt)}]
  [(δ l bool? (b Cs)) {(promote tt)}]
  [(δ l false? ff) {(promote tt)}]
  ; opaque values needing verifying
  [(δ l o? (• Cs))
   {(promote tt)}
   (side-condition (equal? (term Proved)
                           (term (verify (• Cs) (mk-pred o?)))))]
  [(δ l o? (• Cs))
   {(promote ff)}
   (side-condition (equal? (term Refuted)
                           (term (verify (• Cs) (mk-pred o?)))))]
  [(δ l o? (• Cs)) {(promote tt) (promote ff)}]
  ; concrete values that fail predicates
  [(δ l o? V) {(promote ff)}]
  
  ; add1 (partial)
  [(δ l add1 (n Cs)) {(promote ,(add1 (term n)))}]
  [(δ l add1 (• Cs))
   {(• {,nat/c})}
   (side-condition (equal? (term Proved) (term (verify (• Cs) ,nat/c))))]
  [(δ l add1 (• Cs))
   {(blame l add1)}
   (side-condition (equal? (term Refuted) (term (verify (• Cs) ,nat/c))))]
  [(δ l add1 (• Cs)) {(• {,nat/c}) (blame l add1)}]
  [(δ l add1 V) {(blame l add1)}]
  
  ; car (partial)
  [(δ l car ((V_1 V_2) Cs)) {V_1}]
  [(δ l car (• Cs))
   {(promote •)}
   (side-condition (equal? (term Proved) (term (verify (• Cs) ,cons/c))))]
  [(δ l car (• Cs))
   {(blame l car)}
   (side-condition (equal? (term Refuted) (term (verify (• Cs) ,cons/c))))]
  [(δ l car (• Cs)) {(promote •) (blame l car)}]
  [(δ l car V) {(blame l car)}]
  
  ; cdr (partial)
  [(δ l cdr ((V_1 V_2) Cs)) {V_2}]
  [(δ l cdr (• Cs))
   {(promote •)}
   (side-condition (equal? (term Proved) (term (verify (• Cs) ,cons/c))))]
  [(δ l cdr (• Cs))
   {(blame l cdr)}
   (side-condition (equal? (term Refuted) (term (verify (• Cs) ,cons/c))))]
  [(δ l cdr (• Cs)) {(promote •) (blame l cdr)}]
  [(δ l cdr V) {(blame l cdr)}]
  
  ; cons
  [(δ l cons V_1 V_2) {((V_1 V_2) {,cons/c})}]
  
  ; + (partial)
  [(δ l + (m Cs) (n Ds)) {(promote ,(+ (term m) (term n)))}]
  [(δ l + V_1 V_2)
   {(• {,nat/c})}
   (side-condition (equal? (term (Proved Proved))
                           (term (verify V_1 ,nat/c) (verify V_2 ,nat/c))))]
  [(δ l + V_1 V_2)
   {(blame l +)}
   (side-condition (member (term Refuted)
                           (term (verify V_1 ,nat/c) (verify V_2 ,nat/c))))]
  [(δ l + (• Cs) V) {(• {,nat/c}) (blame l +)}]
  [(δ l + V (• Cs)) {(• {,nat/c}) (blame l +)}]
  [(δ l + V_1 V_2) {(blame l +)}]
  
  ;; = (partial)
  ; concrete numeric values
  [(δ l = (m Cs) (n Ds)) {(promote (to-bool ,(= (term m) (term n))))}]
  ; when both operands are guaranteed to be numbers
  [(δ l = V_1 V_2)
   {(promote tt) (promote ff)}
   (side-condition (equal? (term (Proved Proved))
                           (term ((verify V_1 ,nat/c) (verify V_2 ,nat/c)))))]
  ; when either is guaranteed to be non-number
  [(δ l = V_1 V_2)
   {(blame l =)}
   (side-condition (member (term Refuted)
                           (term ((verify V_1 ,nat/c) (verify V_2 ,nat/c)))))]
  ; when nothing is known to opaque value(s)
  [(δ l = (• Cs) V) {(promote tt) (promote ff) (blame l Λ)}]
  [(δ l = V (• Cs)) {(promote tt) (promote ff) (blame l Λ)}]
  ; concrete values known to faile
  [(δ l = V_1 V_2) {(blame l =)}])

;; converts contract to expression
(define-metafunction SCR
  FC : C -> E
  [(FC (μ X C)) (μ X (FC C))]
  [(FC X) X]
  [(FC (flat E)) E]
  [(FC (C ∧ D))
   (λ X (∧ ((FC C) X) ((FC D) X)))
   (where X ,(variable-not-in (term (C D)) (term x)))]
  [(FC (C ∨ D))
   (λ X (∨ ((FC C) X) ((FC D) X)))
   (where X ,(variable-not-in (term (C D)) (term x)))]
  [(FC (C D))
   (λ X (∧ (cons? X) ((FC C) (car X)) ((FC D) (cdr X))))
   (where X ,(variable-not-in (term (C D)) (term x)))])

;; checks whether contract is flat
(define-metafunction SCR
  flat? : C -> #t or #f
  [(flat? (C ↦ (λ X D))) #f]
  [(flat? (C ∨ D)) ,(and (term (flat? C)) (term (flat? D)))]
  [(flat? (C ∧ D)) ,(and (term (flat? C)) (term (flat? D)))]
  [(flat? (C D)) ,(and (term (flat? C)) (term (flat? D)))]
  [(flat? C) #t])
;; checkks whether contract is higher-order
(define-metafunction SCR
  higher-order? : C -> #t or #f
  [(higher-order? C) ,(not (term (flat? C)))])

;; capture-avoiding substitution
(define-metafunction SCR
  subst : any X E -> E
  [(subst X X E) E]
  [(subst Y X E) Y]
  [(subst ((λ X E) Cs) X F) ((λ X E) Cs)] ; var bound; ignore
  [(subst ((λ X E) Cs) Y F)
   (λ Z
     (subst (subst E X Z) Y F)) ; TODO: exponential blow-up risk
   (where Z ,(variable-not-in (term (E Y F)) (term X)))]
  [(subst ((E F) l) X G) ((subst E X G) (subst F X F) l)]
  [(subst (μ X E) X F) (μ X E)] ; var bound, ignore
  [(subst (μ X E) Y F)
   (λ Z
     (subst (subst E X Z) Y F)) ; TODO exponential blow-up risk
   (where Z ,(variable-not-in (term (E Y F)) (term X)))]
  [(subst (mon h f g C E) X F)
   (mon h f g (subst-con C X F) (subst E X F))]
  [(subst (any ...) X E) ((subst any X E) ...)]
  [(subst any X E) any])
(define-metafunction SCR
  subst-con : any X any -> C
  [(subst-con X X E) (flat E)]
  [(subst-con X X any) any]
  [(subst-con X Y any) X]
  [(subst-con (C ↦ (λ X D)) X any) (C ↦ (λ X D))] ; var bound, ignore
  [(subst-con (C ↦ (λ Y D)) X any)
   ((subst-con C X any)
    ↦ (λ Z
        (subst-con (subst-con D Y Z) X any))) ; TODO: exponential blow-up risk
   (where Z ,(variable-not-in (term (C X any)) (term Y)))]
  [(subst-con (flat E) X any) (flat (subst E X any))]
  [(subst-con (μ X C) X any) (μ X C)] ; var bound, ignore
  [(subst-con (μ X C) Y any)
   (μ Z
      (subst-con (subst-con C X Z) Y any)) ; TODO: exponential blow-up risk
   (where Z ,(variable-not-in (term (C Y any)) (term X)))]
  [(subst-con (any ...) X any_1) ((subst-con any X any_1) ...)]
  [(subst-con any X any_1) any])

;; (recursively) wraps prevalues with empty contract sets if not yet so
;; Allows writing SCR terms in a more readable form then wrapped with this
(define-metafunction SCR
  promote : any -> any
  [(promote (λ X any)) ((λ X (promote any)) {})]
  [(promote U) (U {})]
  [(promote A) A]
  [(promote (mon h f g C M))
   (mon h f g (promote-con C) (promote M))]
  [(promote (any ...)) ((promote any) ...)]
  [(promote any) any])
(define-metafunction SCR
  promote-con : any -> any
  [(promote-con (flat any)) (flat (promot any))]
  [(promote-con (C ↦ (λ X D)))
   ((promote-con C) ↦ (λ X (promote-con D)))]
  [(promote-con (any ...)) ((promote any) ...)]
  [(promote-con any) any])

;; converts and/or to if, supporting short-circuiting
(define-metafunction SCR
  desugar-∨ : E ... -> E
  [(desugar-∨) (promote ff)]
  [(desugar-∨ E) E] ; redundant, but reduce junks
  [(desugar-∨ E_0 E ...) (if E_0 (promote tt) (desugar-∨ E ...))])
(define-metafunction SCR
  desugar-∧ : E ... -> E
  [(desugar-∧) (promote tt)]
  [(desugar-∧ E) E] ; redundant, but reduce junks
  [(desugar-∧ E_0 E ...) (if E_0 (desugar-∧ E ...) (promote ff))])

;; checks whether value satisfies contract
(define-metafunction SCR
  verify : V C -> Verified?
  [(verify (U Cs) C)
   Proved
   (side-condition (ormap (λ (c) (term (con~? C ,c))) (term Cs)))]                  
  [(verify V C) Unsure])

;; refines given value with more contract(s)
;; assume value currently does not prove given contract(s)
(define-metafunction SCR
  refine : V C ... -> V
  [(refine (U {C ...}) D ...) (U {D ... C ...})])

;; checks whether two contracts are equivalent
;; may give false negatives
;; currently implemented by checking for α-equivalence
(define-metafunction SCR
  con~? : C C -> any #|bool|#
  [(con~? C D) , (equal? (term (normalize-con () C))
                         (term (normalize-con () D)))])

;; turns any close-variable's use into lexical distance to where it was declared
(define-metafunction SCR
  normalize : [X ...] M -> any
  [(normalize any (f l)) (f l)]
  [(normalize any X) (maybe-index X any)]
  [(normalize any (blame l_1 l_2)) (blame l_1 l_2)]
  [(normalize [X_0 ...] ((λ X E) {C ...}))
   ((λ _ ; kill irrelevant label
      (normalize [X X_0 ...] E))
    {(normalize-con any C) ...})]
  [(normalize any ((V_1 V_2) {C ...}))
   (((normalize any V_1) (normalize any V_2)) {(normalize-con any C) ...})]
  [(normalize any V) V]
  [(normalize [X_0 ...] (μ X E))
   (μ _ ; kill irrelevant label
      (normalize [X X_0 ...] E))]
  [(normalize any (mon h f g C E))
   (mon h f g (normalize-con any C) (normalize any E))]
  [(normalize any_env (any ...)) ((normalize any_env any) ...)]
  [(normalize any_env any) any])
(define-metafunction SCR
  normalize-con : [X ...] C -> any
  [(normalize-con any X) (maybe-index X any)]
  [(normalize-con [X_0 ...] (C ↦ (λ X D)))
   ((normalize-con [X_0 ...] C)
    ↦ (λ _ ; kill irrelevant label
        (normalize-con [X X_0 ...] D)))]
  [(normalize-con any (flat E)) (flat (normalize E))]
  [(normalize-con [X_0 ...] (μ X C))
   (μ _ ; kill irrelevant label
      (normalize-con [X X_0 ...] C))]
  [(normalize-con any (C ∨ D)) ((normalize any C) ∨ (normalize any D))]
  [(normalize-con any (C ∧ D)) ((normalize any C) ∧ (normalize any D))])

;; returns X's position in list, or X itself if not found
(define-metafunction SCR
  maybe-index : X [X ...] -> n or X
  [(maybe-index X []) X]
  [(maybe-index X [X Z ...]) 0]
  [(maybe-index X [Y Z ...]) ,(+ 1 (term (maybe-index X [Z ...])))])

;; substitute V for the newly bound variable in dependent contract
(define-metafunction SCR
  subst-range-con : (C ↦ (λ X D)) V -> C
  [(subst-range-con (C ↦ (λ X D)) V) (subst-con D X V)])

;; generated term to find all possible blames
(define-metafunction SCR
  AMB : E E ... -> E
  [(AMB E) E]
  [(AMB E E_1 ...) (if (• {}) E (AMB E_1 ...))])
(define havoc
  (term (μ y (λ x (AMB (y (x (• {}) †) †)
                       (y (car x †) †)
                       (y (cdr x †) †))))))

;; wrap primitive predicates with lambdas
(define-metafunction SCR
  mk-pred : o? -> C
  [(mk-pred o?) (flat (promote (λ x (o? x †))))])

(define nat/c (term (mk-pred nat?)))
(define bool/c (term (mk-pred bool?)))
(define cons/c (term (mk-pred cons?)))
