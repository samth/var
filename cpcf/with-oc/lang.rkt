#lang racket
(require redex)

(provide
 scpcf δ ev step
 mb default-o acc-o
 flush pop push mk-Γ upd-Γ dom :: Γ:: ! FC split-cons var-from-path
 refine-v refine-with-Γ
 s-map rem-dup non-det:
 c/any C/ANY c/int C/INT c/str C/STR c/bool C/BOOL)

(define-language scpcf
  ; expression
  [(e e′ f) a
            x
            (e e e ...)
            (if e e e)
            (mon c e)
            (μ (x) e)
            ; syntactic sugar:
            (and e e ...)
            (or e e ...)
            (let (x e) e)
            (let ([x e] [x e] ...) e)
            (cond [e e] ... [else e])
            (begin e e ...)
            •]
  [a v ERR]
  [v (λ (x) e) op b]
  
  ; primitives
  [op o1 o2]
  [o1 p? add1 sub1 str-len car cdr]
  [o2 + - * cons]
  [p? tt true? false? bool? str? int? proc? cons? zero?]
  [b n bool s (• CC ...)]
  [(m n) integer]
  [bool #t #f]
  [s string]
  [ψ p? (¬ p?)]
  
  ; environments
  [ρ ([x ↦ C] ...)]
  [O ([x ↦ o′] ...)]
  [Γ ([o′ ↦ ψ ...] ...)]
  
  ; path
  [o ∅ o′]
  [o′ x (acc acc ... x)]
  [acc car cdr]
  
  ; closures
  [C ERR
     (e ρ O)
     (@ C (C o) (C o) ...)
     (C C)
     (mon CC (C o))]
  [V (v ρ O)
     (V V)
     (mon ((c ↦ (λ (x) c)) ρ O) (V o))]
  [CC (c ρ O)]
  
  ; contract
  [c (flat e)
     (or/c c c)
     (and/c c c)
     (cons/c c c)
     (c ↦ (λ (x) c))
     (μ (x) c)
     x]
  
  ; big-step answer
  [A (V Γ o) ERR]
  ; interpreter answer
  [ea n s bool function • (• p? ...) ERR (cons ea ea)]
  
  ; verification answer
  [Verified? Proved Refuted Neither]
  
  [(x y z) variable-not-otherwise-mentioned])

(define c/any (term (flat tt)))
(define C/ANY (term (,c/any [] [])))
(define c/int (term (flat int?)))
(define C/INT (term (,c/int [] [])))
(define c/str (term (flat str?)))
(define C/STR (term (,c/str [] [])))
(define c/bool (term (flat bool?)))
(define C/BOOL (term (,c/bool [] [])))

(define-metafunction scpcf
  ; assume all variables have been (statically) renamed
  ev : e -> {ea ...}
  [(ev e)
   ,(rem-dup (term ((simplify A) ...)))
   (where (A ...) (step [] (e [] [])))])

(define-metafunction scpcf
  simplify : A -> ea
  [(simplify ERR) ERR]
  [(simplify (((λ (x) e) ρ O) Γ o)) function]
  [(simplify ((op ρ O) Γ o)) function]
  [(simplify (((• CC ...) ρ O) Γ o)) ,(match (rem-dup (term (all-preds (CC ...))))
                                        ['() (term •)]
                                        [ps (term (• ,@ ps))])]
  [(simplify ((V_1 V_2) Γ o))
   (cons (simplify (V_1 [] ∅)) (simplify (V_2 [] ∅)))]
  [(simplify ((any ρ O) Γ o)) any])

(define-metafunction scpcf
  all-preds : (CC ...) -> (p? ...)
  [(all-preds (((flat tt) ρ O) any ...)) (all-preds (any ...))]
  [(all-preds (((flat p?) ρ O) any ...))
   ,(cons (term p?) (term (all-preds (any ...))))]
  [(all-preds (any any_1 ...)) (all-preds (any_1 ...))]
  [(all-preds ()) ()])

(define-metafunction scpcf
  step : Γ C -> {A ...}
  
  ; desugar
  [(step Γ ((and e) ρ O)) (step Γ (e ρ O))]
  [(step Γ ((and e_1 e ...) ρ O)) (step Γ ((if e_1 (and e ...) #f) ρ O))]
  [(step Γ ((or e) ρ O)) (step Γ (e ρ O))]
  [(step Γ ((or e_1 e ...) ρ O)) (step Γ ((let (tmp e_1)
                                            (if tmp tmp (or e ...))) ρ O))]
  [(step Γ ((let (x e_x) e) ρ O)) (step Γ (((λ (x) e) e_x) ρ O))]
  [(step Γ ((let ([x e_x]) e) ρ O)) (step Γ (((λ (x) e) e_x) ρ O))]
  [(step Γ ((let ([x e_x] [y e_y] ...) e) ρ O))
   (step Γ ((let (x e_x) (let ([y e_y] ...) e)) ρ O))]
  [(step Γ ((cond [else e]) ρ O)) (step Γ (e ρ O))]
  [(step Γ ((cond [e_1 e_2] any ...) ρ O))
   (step Γ ((if e_1 e_2 (cond any ...)) ρ O))]
  [(step Γ ((begin e) ρ O)) (step Γ (e ρ O))]
  [(step Γ ((begin e_1 e_2 ...) ρ O))
   (step Γ ((let (ignore e_1) (begin e_2 ...)) ρ O))]
  [(step Γ (• ρ O)) (step Γ ((•) ρ O))]
  
  ; val
  [(step Γ V) {((flush Γ V) Γ ∅)}]
  
  ; var
  [(step Γ (x ρ O))
   {((refine-with-Γ V Γ x) Γ (! O x))}
   (where V (! ρ x))]
  [(step Γ (x ρ O))
   ,(non-det:
     [V Γ′ _ ← (term (step (mk-Γ (dom ρ) Γ) ((μ (z) e) ρ_c O_c)))]
     [return: (term (,V (upd-Γ Γ ,Γ′) (! O x)))])
   (where ((μ (z) e) ρ_c O_c) (! ρ x))]
  
  ; app-raw
  [(step Γ ((f e) ρ O))
   ,(non-det:
     [Vf Γ1 __ ← (term (step Γ (f ρ O)))]
     [Vx Γ2 ox ← (term (step ,Γ1 (e ρ O)))]
     (if (redex-match scpcf (o1 any_ρ any_O) Vf)
         (term (δ ,(first Vf) (,Vx ,ox) ,Γ2))
         (non-det:
          [Vy Γ3 oy ← (term (step (mk-Γ (dom ,Vf) ,Γ2)
                                  (@ ,Vf (,Vx (mb ,ox (dom ,Vf))))))]
          [return: (term (,Vy (upd-Γ ,Γ2 ,Γ3) (mb ,oy (dom Γ))))])))]
  [(step Γ ((f e_1 e_2) ρ O))
   ,(non-det:
     [`(,op ,_ρ ,_O) Γ1 __ ← (term (step Γ (f ρ O)))]
     [V1 Γ2 o1 ← (term (step ,Γ1 (e_1 ρ O)))]
     [V2 Γ3 o2 ← (term (step ,Γ2 (e_2 ρ O)))]
     [term (δ ,op (,V1 ,o1) (,V2 ,o2) ,Γ3)])]
  ; app-λ
  [(step Γ (@ ((λ (x) e) ρ O) (V o)))
   ,(non-det:
     [Vy Γ′ oy ← (term (step (push Γ x)
                             (e (:: ρ [x ↦ V]) (:: O [x ↦ (default-o o x)]))))]
     [return: (term (,Vy (pop ,Γ′ x) (mb ,oy (dom Γ))))])]
  ; app-mon
  [(step Γ (@ (mon ((c_1 ↦ (λ (x) c_2)) ρ O) (V_f o_f))
              (V_x o_x)))
   ,(non-det:
     [Vx Γ1 __ ← (term (step Γ (mon (c_1 ρ O) (V_x o_x))))]
     [Vy Γ2 oy ← (term (step (mk-Γ (dom V_f) ,Γ1)
                             (@ V_f (,Vx (mb o_x (dom V_f))))))]
     [Vy′ Γ3 oy′ ← (term (step (push (upd-Γ ,Γ1 ,Γ2) x)
                               (mon (c_2 (:: ρ [x ↦ ,Vx])
                                         (:: O [x ↦ (default-o o_x x)])))))]
     [return: (term (,Vy′ (pop ,Γ3 x) (mb ,oy′ (dom Γ))))])]
  ; app-prim
  [(step Γ (@ (o1 ρ O) (V o))) (δ o1 (V o) Γ)]
  [(step Γ (@ (o2 ρ O) (V_1 o_1) (V_2 o_2) Γ)) (δ o2 (V_1 o_1) (V_2 o_2) Γ)]
  ; app-•
  [(step Γ (@ ((• CC ...) ρ O) (V o)))
   { ERR ; poor man's havoc
     (((• ,@ (term (C-ranges (CC ...)))) [] []) Γ ∅) }]
  
  ; if
  [(step Γ ((if e_1 e_2 e_3) ρ O))
   ,(non-det:
     [V1 Γ1 o1 ← (term (step Γ (e_1 ρ O)))]
     [`(,t? ,_ρ ,_O) _Γ ot ← (term (δ true? (,V1 ,o1) ,Γ1))]
     [if t?
         (term (step ,Γ1 (e_2 ρ O)))
         (term (step ,Γ1 (e_3 ρ O)))])]
  
  ; μ
  [(step Γ ((μ (x) e) ρ O))
   ,(non-det:
     [V Γ′ o ← (term (step (push Γ x) (e (:: ρ [x ↦ ((μ (x) e) ρ O)])
                                         (:: O [x ↦ x]))))]
     [return: (term (,V (pop ,Γ′ x) (mb ,o (dom Γ))))])]
  
  ; mon-distr
  [(step Γ ((mon c e) ρ O))
   ,(non-det:
     [V Γ1 o ← (term (step Γ (e ρ O)))]
     [term (step ,Γ1 (mon (c ρ O) (,V ,o)))])]
  
  ; mon
  [(step Γ (mon (c ρ O) (V o)))
   ,(match (term (FC c))
      [`(,p?) (non-det:
               [V-p? Γ1 _ ← (term (step Γ (,p? ρ O)))]
               [`(,t? ,_ρ ,_O) Γ2 ot ←
                               (term (step (mk-Γ (dom ,V-p?) ,Γ1)
                                           (@ ,V-p? (V (mb o (dom ,V-p?))))))]
               [if t?
                   (let ([Γ3 (term (upd-Γ ,Γ1 ,Γ2))]
                         [o′ (term (mb o (dom Γ)))])
                     (s-map
                      (λ (V′) (term (,V′ ,Γ3 ,o′)))
                      (term (refine-v V (c ρ O)))))
                   (term {ERR})])]
      [_ (match (term c)
           [`(and/c ,c1 ,c2)
            (non-det:
             [V′ Γ′ _ ← (term (step Γ (mon (,c1 ρ O) (V o))))]
             [term (step ,Γ′ (mon (,c2 ρ O) (,V′ o)))])]
           [`(or/c ,c1 ,c2)
            (match-let ([`(,p?) (term (FC c1))]) ; assume flat left disjunction
              (non-det:
               [Vp Γ1 _ ← (term (step Γ (,p? ρ O)))]
               [Vt Γ2 ot ← (term (step (mk-Γ (dom ,Vp) ,Γ1)
                                       (@ ,Vp (V (mb o (dom ,Vp))))))]
               [`(,t? ,_ρ ,_O) _Γ _o ← (term (δ true? (,Vt ,ot) ,Γ2))]
               [if t?
                   (term {((refine-v V (c_1 ρ O))
                           (upd-Γ ,Γ1 ,Γ2)
                           (mb o (dom Γ)))})
                   (term (step (upd-Γ ,Γ1 ,Γ2)
                               (mon (,c2 ρ O) (V (mb o (dom Γ))))))]))]
           [`(cons/c ,c1 ,c2)
            (s-map
             (match-lambda
               [`(,V1 ,V2)
                (non-det:
                 [V1′ Γ1 o1 ← (term (mon (,c1 ρ O) (,V1 (mb (acc-o car o) (dom ρ)))))]
                 [V2′ Γ2 o2 ← (term (mon (,c2 ρ O) (,V2 (mb (acc-o cdr o) (dom ρ)))))]
                 [return: (term ((,V1′ ,V2′) ,Γ2 (mb o (dom Γ))))])]
               [`() 'ERR])
             (term (split-cons (V o) Γ)))]
           [`(μ (,x) ,c′)
            (term (step (push Γ ,x)
                        (mon (,c′ (:: ρ [,x ↦ `((μ (,x) ,c′) ρ O)])
                                  (:: O [,x ↦ ,x]))
                             (V o))))]
           [x (match-let ([`(,c ,ρ ,O) (term (! ρ ,x))])
                (term (step (mk-Γ (dom ,ρ) Γ) (mon (,c ,ρ ,O) (V o)))))])])])

;; extract function contract's domain
(define-metafunction scpcf
  C-ranges : (CC ...) -> (CC ...)
  [(C-ranges ()) ()]
  [(C-ranges (((c_1 ↦ (λ (x) c_2)) ρ O) any ...))
   ,(cons (term (c_2 (:: ρ [x ↦ ((•) [] [])])
                     (:: O [x ↦ x])))
          (term (C-ranges (any ...))))]
  [(C-ranges (any_1 any ...)) (C-ranges (any ...))])

;; 'flushes' all information in Γ to V, after which Γ doesn't know anything
;; new for V
(define-metafunction scpcf
  flush : Γ V -> V
  [(flush Γ ((λ (x) e) ρ O)) ((λ (x) e) (flush-ρ Γ ρ) O)]
  [(flush Γ (mon (c ρ O) (V o))) (mon (c (flush-ρ Γ ρ) O) (V o))]
  [(flush Γ V) V]) ; for now

;; 'flushes' all propositions in Γ into ρ as refinining contracts for •'s
(define-metafunction scpcf
  flush-ρ : Γ ρ -> ρ
  [(flush-ρ [] ρ) ρ]
  [(flush-ρ ([x ↦ ψ ...] any ...) (any_1 ... [x ↦ ((• CC ...) ρ O)] any_2 ...))
   (flush-ρ (any ...)
            (any_1 ... [x ↦ ((• (mk-CC () ψ) ... CC ...) [] [])] any_2 ...))]
  [(flush-ρ ([(acc ... x) ↦ ψ ...] any ...)
            (any_1 ... [x ↦ ((• CC ...) ρ O)] any_2 ...))
   (flush-ρ (any ...)
            (any_1 ... [x ↦ ((• (mk-CC (acc ...) ψ) ... CC ...) [] [])] any_2 ...))]
  [(flush-ρ (any_1 any ...) ρ) (flush-ρ (any ...) ρ)])

;; check whether value satisfies contract
(define-metafunction scpcf
  V⊢? : V CC -> Verified?
  [(V⊢? ((• any_1 ... CC any_2 ...) ρ O) CC_1)
   Proved
   (where #t (C-implies? CC CC_1))]
  [(V⊢? ((• any_1 ... CC any_2 ...) ρ O) CC_1)
   Refuted
   (where #t (C-excludes? CC CC_1))]
  [(V⊢? V CC) Neither])

;; uses existing information to check whether the predicate holds
(define-metafunction scpcf
  ⊢? : (CC ...) Γ o p? -> Verified?
  ; Γ is easier/cheaper, so use it first
  [(⊢? (CC ...) Γ o p?) ,(match (term (Γ⊢? Γ o p?))
                           ['Proved (term Proved)]
                           ['Refuted (term Refuted)]
                           ['Neither (term (C⊢? (CC ...) p?))])])

;; checks whether contract set can prove/refute predicate
(define-metafunction scpcf
  C⊢? : (CC ...) p? -> Verified?
  [(C⊢? (any_1 ... ((flat p?) ρ O) any_2 ...) p?_1)
   Proved
   (where #t (implies? p? p?_1))]
  [(C⊢? (any_1 ... ((flat p?) ρ O) any_2 ...) p?_1)
   Refuted
   (where #t (excludes? p? p?_1))]
  [(C⊢? any p?) Neither])

;; checks whether proposition set can prove/refute predicate
(define-metafunction scpcf
  Γ⊢? : Γ o p? -> Verified?
  [(Γ⊢? (any_1 ... [o′ ↦ any_3 ... p? any_4 ...] any_2 ...) o′ p?_1)
   Proved
   (where #t (implies? p? p?_1))]
  [(Γ⊢? (any_1 ... [o′ ↦ any_3 ... p? any_4 ...] any_2 ...) o′ p?_1)
   Refuted
   (where #t (excludes? p? p?_1))]
  [(Γ⊢? (any_1 ... [o′ ↦ any_3 ... (¬ p?) any_4 ...] any_2 ...) o′ p?_1)
   Refuted
   (where #t (implies? p?_1 p?))]
  [(Γ⊢? any_Γ any_o any_p?) Neither])

;; checks predicates on concrete values
(define-metafunction scpcf
  concrete-check : p? V -> bool
  [(concrete-check int? (n ρ O)) #t]
  [(concrete-check zero? (0 ρ O)) #t]
  [(concrete-check str? (s ρ O)) #t]
  [(concrete-check false? (#f ρ O)) #t]
  [(concrete-check false? V) #f]
  [(concrete-check bool? (bool ρ O)) #t]
  [(concrete-check proc? ((λ (x) e) ρ O)) #t]
  [(concrete-check true? (#f ρ O)) #f]
  [(concrete-check true? V) #t]
  [(concrete-check cons? (V_1 V_2)) #t]
  [(concrete-check p? V) #f])

;; refines value with given (closed) contract
(define-metafunction scpcf
  refine-v : V CC -> {V ...}
  [(refine-v ((• CC_1 ...) ρ O) CC)
   ,(s-map
     (λ (Cs) (term ((• ,@ Cs) ρ O)))
     (term (refine (CC_1 ...) CC)))]
  [(refine-v V CC) {V}])

;; refines set of contracts with another contract
(define-metafunction scpcf
  refine : {CC ...} CC -> {{CC ...} ...}
  
  ; special cases where we can do something smarter
  [(refine {any_1 ... CC_1 any_2 ...} CC_2)
   {{any_1 ... CC_1 any_2 ...}}
   (where #t (C-implies? CC_1 CC_2))] ; refining contract is redundant
  [(refine {any_1 ... CC_1 any_2 ...} CC_2)
   {{any_1 ... CC_2 any_2 ...}}
   (where #t (C-implies? CC_2 CC_1))] ; one of the old contract is redundant
  [(refine {any_1 ... CC_1 any_2 ...} CC_2)
   {}
   (where #t (C-excludes? CC_1 CC_2))] ; the refinement is bullshit
  
  ; general cases
  [(refine any ((or/c c_1 c_2) ρ O)) ; split disjunction for better precision
   ,(∪ (term (refine any (c_1 ρ O))) (term (refine any (c_2 ρ O))))]
  [(refine any ((and/c c_1 c_2) ρ O)) ; break conjunction into smaller refinements
   ,(s-map
     (λ (Cs)
       (term (refine ,Cs (c_2 ρ O))))
     (term (refine any (c_2 ρ O))))]
  [(refine any ((μ (x) c) ρ O)) ; unroll recursive contract
   (refine any (c (:: [x ↦ ((μ (x) c) ρ O)] ρ)
                  (:: [x ↦ x] O)))]
  [(refine any (x ρ O)) (refine any (! ρ x))]
  [(refine {CC ...} CC_1) {{CC_1 CC ...}}])

;; checks whether first contract (definitely) implies second
;; may give false negative
(define-metafunction scpcf
  C-implies? : CC CC -> bool
  [(C-implies? ((flat p?) ρ O) ((flat p?_1) ρ_1 O_1)) (implies? p? p?_1)]
  [(C-implies? CC_1 CC_2) #f])

;; checks whether first contract (definitely) contradicts second
;; may give false negative
(define-metafunction scpcf
  C-excludes? : CC CC -> bool
  [(C-excludes? ((flat p?) ρ O) ((flat p?_1) ρ_1 O_1)) (excludes? p? p?_1)]
  [(C-excludes? CC_1 CC_2) #f])

;; checks whether first proposition (definitely) implies second
(define-metafunction scpcf
  ψ-implies? : ψ ψ -> bool
  [(ψ-implies? p? p?_1) (implies? p? p?_1)]
  [(ψ-implies? (¬ p?) (¬ p?_1)) (implies? p?_1 p?)]
  [(ψ-implies? p? (¬ p?_1)) (excludes? p? p?_1)]
  [(ψ-implies? (¬ true?) false?) #t]
  [(ψ-implies? (¬ false? true?)) #t]
  [(ψ-implies? (¬ p?) p?_1) #f])

;; checks whether first predicate implies second
(define-metafunction scpcf
  implies? : p? p? -> bool
  [(implies? p? tt) #t]
  [(implies? p? p?) #t]
  [(implies? false? true?) #f]
  [(implies? p? true?) #t]
  [(implies? p? p?_1) #f])

;; checks whether first predicate contradicts second
(define-metafunction scpcf
  excludes? : p? p? -> bool
  [(excludes? p? p?_1)
   ,(ormap (λ (S) (and (not (equal? (term p?) (term p?_1)))
                       (member (term p?) S)
                       (member (term p?_1) S) #t #| #t here to force bool |#))
           `((true? false?)
             (int? str? bool? proc? cons?)))])



;; use propositions in Γ to refine value
(define-metafunction scpcf
  refine-with-Γ : V Γ x -> V
  [(refine-with-Γ ((• CC ...) ρ O) ([x ↦ ψ ...] any ...) x)
   (refine-with-Γ ((• (mk-CC () ψ) ... CC ...) ρ O) (any ...) x)]
  [(refine-with-Γ ((• CC ...) ρ O) ([(acc ... x) ↦ ψ ...] any ...) x)
   (refine-with-Γ ((• (mk-CC (acc ...) ψ) ... CC ...) ρ O) (any ...) x)]
  [(refine-with-Γ ((• CC ...) ρ O) (any any_1 ...) x)
   (refine-with-Γ ((• CC ...) ρ O) (any_1 ...) x)]
  [(refine-with-Γ V Γ x) V])

;; makes (closed) contract out of proposition
(define-metafunction scpcf
  mk-CC : (acc ...) ψ -> CC
  [(mk-CC any p?) ((mk-c any (flat p?)) [] [])]
  ; lose precision for now until we have not/c?
  [(mk-CC any (¬ p?)) ((flat tt) [] [])])
;; constructs contract for given path of accessors
(define-metafunction scpcf
  mk-c : (acc ...) c -> c
  [(mk-c () c) c]
  [(mk-c (car acc ...) c) (mk-c (acc ...) (cons/c c ,c/any))]
  [(mk-c (cdr acc ...) c) (mk-c (acc ...) (cons/c ,c/any c))])

;; removes x from Γ's domain
(define-metafunction scpcf
  pop : Γ x -> Γ
  [(pop () x) ()]
  [(pop ([x ↦ any ...] any_1 ...) x) (pop (any_1 ...) x)]
  [(pop ([(any_acc ... x) ↦ any ...] any_1 ...) x) (pop (any_1 ...) x)]
  [(pop (any any_1 ...) x) ,(cons (term any) (term (pop (any_1 ...) x)))])

;; overrides Γ with [x ↦ tt]
(define-metafunction scpcf
  push : Γ x -> Γ
  [(push Γ x) ,(cons (term [x ↦ tt]) (term (pop Γ x)))])

;; returns environment's domain. (overloaded on closures)
(define-metafunction scpcf
  dom : any -> {x ...}
  [(dom ([o′ ↦ any ...] ...)) ,(rem-dup (term ((var-from-path o′) ...)))]
  ; overloaded
  [(dom (e ρ O)) (dom ρ)]
  [(dom (mon (c ρ O) (C o))) (dom ρ)])
;; extracts variable from path
(define-metafunction scpcf
  var-from-path : o′ -> x
  [(var-from-path x) x]
  [(var-from-path (any ... x)) x])

;; makes proposition environment with given domain and updates it with Γ
(define-metafunction scpcf
  mk-Γ : {x ...} Γ -> Γ
  [(mk-Γ {x ...} Γ) (upd-Γ ([x ↦ tt] ...) Γ)])

;; updates Γ1 with propositions from Γ2 if they talk about the same variable
(define-metafunction scpcf
  upd-Γ : Γ Γ -> Γ
  [(upd-Γ any []) any]
  [(upd-Γ (any_1 ... [o′ ↦ ψ ...] any_2 ...) ([o′ ↦ ψ_1 ...] any_3 ...))
   (upd-Γ (any_1 ... [o′ ↦ ψ_1 ...] any_2 ...) (any_3 ...))]
  [(upd-Γ (any_1 ... [x ↦ ψ ...] any_2 ...) ([(acc ... x) ↦ ψ_1 ...] any_3 ...))
   (upd-Γ ([(acc ... x) ↦ ψ_1 ...] any_1 ... [x ↦ ψ ...] any_2 ...) (any_3 ...))]
  [(upd-Γ (any_1 ... [(acc ... x) ↦ ψ ...] any_2 ...) ([x ↦ ψ_1 ...] any_3 ...))
   (upd-Γ ([x ↦ ψ_1 ...] any_1 ... [(acc ... x) ↦ ψ ...] any_2 ...) (any_3 ...))]
  [(upd-Γ any (any_1 any_2 ...)) (upd-Γ any (any_2 ...))])

;; extends/updates environment
(define-metafunction scpcf
  :: : ([x ↦ any] ...) [x ↦ any] -> ([x ↦ any] ...)
  [(:: (any_1 ... [x ↦ any] any_2 ...) [x ↦ any_3])
   (any_1 ... [x ↦ any_3] any_2 ...)]
  [(:: (any ...) [x ↦ any_1]) ([x ↦ any_1] any ...)])

;; looks up environment at given key assumed exists
(define-metafunction scpcf
  ! : ([x ↦ any] ...) x -> any
  [(! (any_1 ... [x ↦ any] any_2 ...) x) any])

;; updates proposition environment with proposition
(define-metafunction scpcf
  Γ:: : Γ ψ o -> Γ
  [(Γ:: any_Γ any_ψ ∅) any_Γ]
  [(Γ:: (any ... [o ↦ tt] any_1 ...) ψ o) (any ... [o ↦ ψ] any_1 ...)]
  [(Γ:: (any ... [o ↦ ψ_1 ... ψ ψ_n ...] any_1 ...) ψ o)
   (any ... [o ↦ ψ_1 ... ψ ψ_n ...] any_1 ...)]
  [(Γ:: (any_1 ... [o ↦ any ...] any_2 ...) ψ o)
   (any_1 ... [o ↦ ψ any ...] any_2 ...)]
  [(Γ:: (any_1 ... [o_k ↦ ψ_k ...] any_2 ...) ψ o)
   ([o ↦ ψ] any_1 ... [o_k ↦ ψ_k ...] any_2 ...)
   (where (x x) ((var-from-path o_k) (var-from-path o)))])

;; keeps the path only when it's in given domain
(define-metafunction scpcf
  mb : o {x ...} -> o
  [(mb x {z ... x y ...}) x]
  [(mb (acc ... x) {z ... x y ...}) (acc ... x)]
  [(mb o any) ∅])

;; use the first path unless it is ∅ (then resort to second one)
(define-metafunction scpcf
  default-o : o o′ -> o′
  [(default-o ∅ o′) o′]
  [(default-o o′ any) o′])

;; applies accessor on path
(define-metafunction scpcf
  acc-o : acc o -> o
  [(acc-o acc ∅) ∅]
  [(acc-o acc x) (acc x)]
  [(acc-o acc (acc_1 ... x)) (acc acc_1 ... x)])

;; flattens flat contract into expression, or #f for higher-order contracts
(define-metafunction scpcf
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

;; interprets primitive ops
(define-metafunction scpcf
  δ : op (V o) ... Γ -> {A ...}
  
  ; add1
  [(δ add1 ((n ρ O) o) Γ) {((,(add1 (term n)) [] []) Γ ∅)}]
  [(δ add1 (((• CC ...) ρ O) o) Γ)
   ,(match (term (⊢? (CC ...) Γ o int?))
      ['Proved (term {(((• ,C/INT) [] []) Γ ∅)})]
      ['Refuted (term {ERR})]
      ['Neither (term {(((• ,C/INT) [] []) (Γ:: Γ int? o) ∅)
                       ERR})])]
  [(δ add1 (V o) Γ) {ERR}]
  
  ; sub1
  [(δ sub1 ((n ρ O) o) Γ) {((,(sub1 (term n)) [] []) Γ ∅)}]
  [(δ sub1 (((• CC ...) ρ O) o) Γ)
   ,(match (term (⊢? (CC ...) Γ o int?))
      ['Proved (term {(((• ,C/INT) [] []) Γ ∅)})]
      ['Refuted (term {ERR})]
      ['Neither (term {(((• ,C/INT) [] []) (Γ:: Γ int? o) ∅)
                       ERR})])]
  [(δ sub1 (V o) Γ) {ERR}]
  
  ; str-len
  [(δ str-len ((s ρ O) o) Γ) {((,(string-length (term s)) [] []) Γ o)}]
  [(δ str-len (((• CC ...) ρ O) o) Γ)
   ,(match (term (⊢? (CC ...) Γ o str?))
      ['Proved (term {(((• ,C/INT) [] []) Γ ∅)})]
      ['Refuted (term {ERR})]
      ['Neither (term {(((• ,C/INT) [] []) (Γ:: Γ str? o) ∅)
                       ERR})])]
  [(δ str-len (V o) Γ) {ERR}]
  
  ; car, cdr
  [(δ car (V o) Γ)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V1 (Γ:: Γ cons? o) (acc-o car o)))]
       [`() (term ERR)])
     (term (split-cons (V o) Γ)))]
  [(δ cdr (V o) Γ)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V2 (Γ:: Γ cons? o) (acc-o cdr o)))]
       [`() (term ERR)])
     (term (split-cons (V o) Γ)))]
  
  ; +
  [(δ + ((m ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   {((,(+ (term m) (term n)) [] []) Γ ∅)}]
  [(δ + (((• CC ...) ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   (δ + (((• CC ...) [] []) o_m) (((• ,C/INT) [] []) o_n) Γ)]
  [(δ + ((m ρ_m O_m) o_m) (((• CC ...) ρ_n O_n) o_n) Γ)
   (δ + (((• ,C/INT) [] []) o_m) (((• CC ...) [] []) o_n) Γ)]
  [(δ + (((• CC_1 ...) ρ_m O_m) o_m) (((• CC_2 ...) ρ_n O_n) o_n) Γ)
   ,(match (term ((⊢? (CC_1 ...) Γ o_m int?) (⊢? (CC_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERR})]
      [_ (term {(((• ,C/INT) [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                ERR})])]
  
  ; -
  [(δ - ((m ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   {((,(- (term m) (term n)) [] []) Γ ∅)}]
  [(δ - (((• CC ...) ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   (δ - (((• CC ...) [] []) o_m) (((• ,C/INT) [] []) o_n) Γ)]
  [(δ - ((m ρ_m O_m) o_m) (((• CC ...) ρ_n O_n) o_n) Γ)
   (δ - (((• ,C/INT) [] []) o_m) (((• CC ...) [] []) o_n) Γ)]
  [(δ - (((• CC_1 ...) ρ_m O_m) o_m) (((• CC_2 ...) ρ_n O_n) o_n) Γ)
   ,(match (term ((⊢? (CC_1 ...) Γ o_m int?) (⊢? (CC_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERR})]
      [_ (term {(((• ,C/INT) [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                ERR})])]
  
  ; *
  [(δ * ((m ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   {((,(* (term m) (term n)) [] []) Γ ∅)}]
  [(δ * (((• CC ...) ρ_m O_m) o_m) ((n ρ_n O_n) o_n) Γ)
   (δ * (((• CC ...) [] []) o_m) (((• ,C/INT) [] []) o_n) Γ)]
  [(δ * ((m ρ_m O_m) o_m) (((• CC ...) ρ_n O_n) o_n) Γ)
   (δ * (((• ,C/INT) [] []) o_m) (((• CC ...) [] []) o_n) Γ)]
  [(δ * (((• CC_1 ...) ρ_m O_m) o_m) (((• CC_2 ...) ρ_n O_n) o_n) Γ)
   ,(match (term ((⊢? (CC_1 ...) Γ o_m int?) (⊢? (CC_2 ...) Γ o_n int?)))
      [`(Proved Proved) (term {(((• ,C/INT) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERR})]
      [_ (term {(((• ,C/INT) [] [])
                 (Γ:: (Γ:: Γ int? o_m) int? o_n)
                 ∅)
                ERR})])]
  
  ; cons
  [(δ cons (V_1 o_1) (V_2 o_2) Γ) {((V_1 V_2) Γ ∅)}]
  
  ; predicates
  [(δ tt (V o) Γ) {((#t [] []) Γ ∅)}]
  [(δ p? (((• CC ...) ρ O) o) Γ)
   ,(match (term (⊢? (CC ...) Γ o p?))
      ['Proved (term {((#t [] []) (Γ:: Γ p? o) ∅)})]
      ['Refuted (term {((#f [] []) (Γ:: Γ (¬ p?) o) ∅)})]
      ['Neither (term {((#t [] []) (Γ:: Γ p? o) ∅)
                       ((#f [] []) (Γ:: Γ (¬ p?) o) ∅)})])]
  [(δ p? (V o) Γ)
   ,(match (term (concrete-check p? V))
      [#t (term {((#t [] []) (Γ:: Γ p? o) ∅)})]
      [#f (term {((#f [] []) (Γ:: Γ (¬ p?) o) ∅)})])]
  
  [(δ op (V o) ... Γ) {ERR}])

;; split pair closure into 2, or () indicating not a pair
(define-metafunction scpcf
  split-cons : (V o) Γ -> {(V ...) ...} ; (V ...) being (V V) or ()
  [(split-cons ((V_1 V_2) o) Γ) {(V_1 V_2)}]
  [(split-cons (((• CC ...) ρ O) o) Γ)
   ,(match (term (acc-cons (CC ...) ()))
      ['() (match (term (Γ⊢? Γ o cons?))
             ['Proved (term { (((•) [] []) ((•) [] [])) })]
             ['Refuted (term {()})]
             ['Neither (term { (((•) [] []) ((•) [] []))
                               () })])]
      [acc (s-map
            (match-lambda
              [`(,Cs1 ,Cs2) (term (((• ,@ Cs1) [] []) ((• ,@ Cs2) [] [])))]
              ['() (term ())])
            acc)])]
  [(split-cons (V o) Γ) {()}])
(define-metafunction scpcf
  acc-cons : (CC ...) {((CC ...) ...) ...} -> {((CC ...) ...) ...}
  [(acc-cons () any) any]
  [(acc-cons ([(or/c c_1 c_2) ρ O] any ...) any_acc)
   ,(∪ (term (acc-cons ((c_1 ρ O) any ...) any_acc))
       (term (acc-cons ((c_2 ρ O) any ...) any_acc)))]
  [(acc-cons ([(and/c c_1 c_2) ρ O] any ...) any_acc)
   (acc-cons ([c_1 ρ O] [c_2 ρ O] any ...) any_acc)]
  [(acc-cons ([(c ↦ any ...) ρ O] any_1 ...) any_acc) '(())]
  [(acc-cons ([(cons/c c_1 c_2) ρ O] any ...) any_acc)
   (acc-cons (any ...)
             ,(match (term any_acc)
                ['() (term {([(c_1 ρ O)] [(c_2 ρ O)])})]
                [_ (s-map
                    (match-lambda
                      [`(,CC1 ,CC2) (term (([c_1 ρ O] ,@ CC1) ([c_2 ρ O] ,@ CC2)))]
                      ['() (term ())])
                    (term any_acc))]))]
  [(acc-cons ([x ρ O] any ...) any_acc) (acc-cons ([! ρ x] any ...) any_acc)]
  [(acc-cons ([(μ (x) c) ρ O] any ...) any_acc)
   (acc-cons ((c (:: ρ [x ↦ ((μ (x) c) ρ O)]) (:: O [x ↦ x])) any ...) any_acc)]
  [(acc-cons ([(flat p?) ρ O] any ...) any_acc)
   (acc-cons (any ...) ,(match (term any_acc)
                          ['() '([() ()])]
                          [x x]))
   (where #t (implies? p? cons?))]
  [(acc-cons ([(flat p?) ρ O] any ...) any_acc)
   '()
   (where #t (excludes? p? cons?))]
  [(acc-cons (any any_1 ...) any_acc) (acc-cons (any_1 ...) any_acc)])



;;;;; HELPER stuff for non-determinism

;; kills duplicates
;; rem-dup : [Listof X] -> [Listof X]
(define rem-dup (compose set->list list->set))

;; like map, but kills duplicates
;; s-map : [X -> Y] [Listof X] -> [Listof Y]
(define (s-map f xs)
  (rem-dup (map f xs)))

;; non-det : [X -> [Listof Y]] [Listof X] -> [Listof Y]
(define (non-det f xs)
  (rem-dup (apply append (map f xs))))

;; ∪ : [Listof X] [Listof X] -> [Listof X]
(define (∪ xs ys)
  (rem-dup (append xs ys)))

(define-syntax non-det:
  (syntax-rules (← return:)
    [(_ [V Γ o ← e] e1 e2 ...)
     (non-det
      (match-lambda
        [`(,V ,Γ ,o) (non-det: e1 e2 ...)]
        ['ERR '{ERR}])
      e)]
    [(_ e1 e2 e3 ...) (non-det (λ (_) (non-det: e2 e3 ...))
                               e1)]
    [(_ (return: x ...)) (rem-dup (list x ...))]
    [(_ e) e]))