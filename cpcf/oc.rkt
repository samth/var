#lang racket
(require redex)

(define-language oc
  ; expression
  [(e e′ f) v
            x
            (e e e ...)
            (if e e e)
            (op1 e)
            (op2 e e)
            (μ (x) e)
            (mon c e)
            
            ; syntactic sugar
            (and e e ...)
            (or e e ...)
            (begin e e ...)
            (let [x e] e)
            (let ([x e] [x e] ...) e)
            (cond [e e] ... [else e])]
  
  ; value
  [v d
     (λ (x x ...) e)
     •
     (• p? ...) #|value refined by predicates|#]
  
  ; path
  [o ∅ o′]
  [o′ x (car o′) (cdr o′)] ; TODO: could <o,o> be useful?
  
  ; closed value (with the exception of μx.e)
  [V (v E O)
     ((μ (x) e) E O)
     (V V)]
  
  ; environments
  [E ([x ↦ V] ...)]
  [O ([x ↦ o′] ...)]
  [Γ ([o′ ↦ ψs ...] ...)]
  
  ; predicate
  [ψ p? (¬ p?)]
  [ψs (ψ ...)]
  
  ; evaluation answer
  [A (V Γ o)
     ERROR]
  
  ; contract
  [c (flat e)
     (c ↦ (λ (x) c))
     (or/c c c)
     (and/c c c)
     (cons/c c c)
     (μ (x) c)
     x
     
     ; syntactic sugar
     (c ↦ c)]
  
  ; closed contract
  [C (c E)]
  
  ; verification answer
  [Verified? Proved Refuted Neither]
  
  [op1 p? add1 sub1 str-len car cdr]
  [op2 + - * cons]
  [op op1 op2]
  [p? zero? int? str? cons? true? false? bool? proc?]
  [d b n s]
  [(m n) integer]
  [s string]
  [b #t #f]
  [(x y z) variable-not-otherwise-mentioned])

;; evaluates program, returning only result
(define-metafunction oc
  eval : e -> any
  [(eval e) ,(remdup (term ((simplify A) ...)))
            (where (A ...) (eval′ e))])

;; evaluates, returning full state with Γ containing assumptions
(define-metafunction oc
  eval′ : e -> {A ...}
  [(eval′ e) (⇓′ [] [] [] e)])

;; applies big-step semantics on a state of (E O Γ e), useful for debugging
(define-metafunction oc
  ⇓′ : E O Γ e -> {A ...}
  [(⇓′ E O Γ e) (⇓ E O Γ (desug e))])

;; big-step semantics
(define-metafunction oc
  ⇓ : E O Γ e -> {A ...}
  
  ; vals
  [(⇓ E O Γ d) {((d [] []) Γ ∅)}]
  [(⇓ E O Γ (• p? ...)) {(((• p? ...) [] []) Γ ∅)}]
  [(⇓ E O Γ (λ (x) e)) {(((λ (x) e) E O) Γ ∅)}]
  
  ; var
  [(⇓ E O Γ x)
   ,(match (term (! x E))
      [`((μ (,z) ,e) ,Eμ ,Oμ) ; μx.e is not yet a value
       (non-det:
        [V1 Γ1 o1 ← (term (⇓ ,Eμ ,Oμ Γ (μ (,z) ,e)))]
        [return: (term (,V1 ,Γ1 x))])]
      [V (term {(,V Γ (! x O))})])]
  
  ; app
  [(⇓ E O Γ (f e))
   ,(non-det:
     [Vλ Γ1 oλ ← (term (⇓ E O Γ f))]
     [match Vλ
       [`((λ (,x) ,e′) ,Eλ ,Oλ)
        (non-det:
         [V Γ2 o2 ← (term (⇓ E O ,Γ1 e))]
         [if (equal? x o2) ; void precision loss for (let (x x) ...) cases
             (term (⇓ (:: [,x ↦ ,V] ,Eλ)
                      (:: [,x ↦ ,x] ,Oλ)
                      ,Γ2
                      ,e′))
             (non-det:
              [V3 Γ3 o3 ← (term (⇓ (:: [,x ↦ ,V] ,Eλ)
                                   (:: [,x ↦ (default-o ,x ,o2)] ,Oλ)
                                   (Γ-push-var ,x ,Γ2)
                                   ,e′))]
              [return: (term (,V3 (Γ-pop-var ,x ,Γ3) ,o3))])])]
       [`((• ,p? ...) ,Eλ ,Oλ)
        (match (term (Γ⊢? proc? ,p? ,Γ1 oλ))
          ['Refuted (return: (term ERROR))]
          [(or 'Proved 'Neither) (return: (term (((•) [] []) ,Γ1 ∅))
                                          (term ERROR))])]])]
  
  ; if
  [(⇓ E O Γ (if e_1 e_2 e_3))
   ,(non-det:
     [V1 Γ1 o1 ← (term (⇓ E O Γ e_1))]
     [`(,t? ,_E ,_O) _Γ _o ← (term (δ true? ,V1 ,Γ1 ,o1))]
     [if t?
         (term (⇓ E O ,Γ1 e_2))
         (term (⇓ E O ,Γ1 e_3))])]
  
  ; μ
  [(⇓ E O Γ (μ (x) e))
   ,(non-det:
     [V1 Γ1 o1 ← (term (⇓ (:: [x ↦ ((μ (x) e) E O)] E)
                          (:: [x ↦ x] O)
                          (Γ-push-var x Γ)
                          e))]
     [return: (term (,V1 (Γ-pop-var x ,Γ1) ,o1))])]
  
  ; mon
  ;  [(⇓ E O Γ (mon c e))
  ;   ,(match-non-det:
  ;     (term (⇓ E O Γ e))
  ;     ['ERROR (term {ERROR})]
  ;     [`(,V1 ,Γ1 ,o1)
  ;      (match-non-det:
  ;       (FC c)
  ;       [`(,pred) (
  
  ; δ
  [(⇓ E O Γ (op1 e))
   ,(non-det:
     [V1 Γ1 o1 ← (term (⇓ E O Γ e))]
     [term (δ op1 ,V1 ,Γ1 ,o1)])]
  [(⇓ E O Γ (op2 e_1 e_2))
   ,(non-det:
     [V1 Γ1 o1 ← (term (⇓ E O Γ e_1))]
     [V2 Γ2 o2 ← (term (⇓ E O ,Γ1 e_2))]
     [term (δ op2 ,V1 ,V2 ,Γ2 ,o1 ,o2)])])

;; applies primitive ops, returns result + new propositions + path object
(define-metafunction oc
  δ : op V ... Γ o ... -> {A ...}
  
  ; add1
  [(δ add1 (n E O) Γ o) {((,(add1 (term n)) [] []) Γ ∅)}]
  [(δ add1 ((• p? ...) E O) Γ o)
   ,(match (term (Γ⊢? int? (p? ...) Γ o))
      ['Proved (term {(((• int?) [] []) Γ ∅)})]
      ['Refuted (term {ERROR})]
      ['Neither (term {(((• int?) [] []) (Γ:: int? o Γ) ∅)
                       ERROR})])]
  [(δ add1 V Γ o) {ERROR}]
  
  ; sub1
  [(δ sub1 (n E O) Γ o) {((,(sub1 (term n)) [] []) Γ ∅)}]
  [(δ sub1 ((• p? ...) E O) Γ o)
   ,(match (term (Γ⊢? int? (p? ...) Γ o))
      ['Proved (term {(((• int?) [] []) Γ ∅)})]
      ['Refuted (term {ERROR})]
      ['Neither (term {(((• int?) [] []) (Γ:: int? o Γ) ∅)
                       ERROR})])]
  [(δ sub1 V Γ o) {ERROR}]
  
  ; str-len
  [(δ str-len (s E O) Γ o) {((,(string-length (term s)) [] []) Γ o)}]
  [(δ str-len ((• p? ...) E O) Γ o)
   ,(match (term (Γ⊢? str? (p? ...) Γ o))
      ['Proved (term {(((• int?) [] []) Γ o)})]
      ['Refuted (term {ERROR})]
      ['Neither (term {(((• int?) [] []) (Γ:: str? o Γ) ∅)
                       ERROR})])]
  [(δ str-len V Γ o) {ERROR}]
  
  ; car, cdr
  [(δ car V Γ o)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V1 (Γ:: cons? o Γ) (car-o o)))]
       [`() (term ERROR)])
     (term (split-cons V Γ o)))]
  [(δ cdr V Γ o)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V2 (Γ:: cons? o Γ) (cdr-o o)))]
       [`() (term ERROR)])
     (term (split-cons V Γ o)))]
  
  ; +
  [(δ + (m [] []) (n [] []) Γ o_1 o_2)
   {((,(+ (term m) (term n)) [] []) Γ ∅)}]
  [(δ + ((• p? ...) E_1 O_1) (n E_2 O_2) Γ o_1 o_2)
   (δ + ((• p? ...) [] []) ((• int?) [] []) Γ o_1 o_2)]
  [(δ + (m E_1 O_1) ((• p? ...) E_2 O_2) Γ o_1 o_2)
   (δ + ((• int?) [] []) ((• p? ...) [] []) Γ o_1 o_2)]
  [(δ + ((• p?_1 ...) E_1 O_1) ((• p?_2 ...) E_2 O_2) Γ o_1 o_2)
   ,(match (term ((Γ⊢? int? (p?_1 ...) Γ o_1) (Γ⊢? int? (p?_2 ...) Γ o_2)))
      [`(Proved Proved) (term {(((• int?) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERROR})]
      [_ (term {(((• int?) [] []) Γ ∅) ERROR})])]
  
  ; -
  [(δ - (m [] []) (n [] []) Γ o_1 o_2)
   {((,(- (term m) (term n)) [] []) Γ ∅)}]
  [(δ - ((• p? ...) E_1 O_1) (n E_2 O_2) Γ o_1 o_2)
   (δ - ((• p? ...) [] []) ((• int?) [] []) Γ o_1 o_2)]
  [(δ - (m E_1 O_1) ((• p? ...) E_2 O_2) Γ o_1 o_2)
   (δ - ((• int?) [] []) ((• p? ...) [] []) Γ o_1 o_2)]
  [(δ - ((• p?_1 ...) E_1 O_1) ((• p?_2 ...) E_2 O_2) Γ o_1 o_2)
   ,(match (term ((Γ⊢? int? (p?_1 ...) Γ o_1) (Γ⊢? int? (p?_2 ...) Γ o_2)))
      [`(Proved Proved) (term {(((• int?) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERROR})]
      [_ (term {(((• int?) [] []) Γ ∅) ERROR})])]
  
  ; *
  [(δ * (m [] []) (n [] []) Γ o_1 o_2)
   {((,(* (term m) (term n)) [] []) Γ ∅)}]
  [(δ * ((• p? ...) E_1 O_1) (n E_2 O_2) Γ o_1 o_2)
   (δ * ((• p? ...) [] []) ((• int?) [] []) Γ o_1 o_2)]
  [(δ * (m E_1 O_1) ((• p? ...) E_2 O_2) Γ o_1 o_2)
   (δ * ((• int?) [] []) ((• p? ...) [] []) Γ o_1 o_2)]
  [(δ * ((• p?_1 ...) E_1 O_1) ((• p?_2 ...) E_2 O_2) Γ o_1 o_2)
   ,(match (term ((Γ⊢? int? (p?_1 ...) Γ o_1) (Γ⊢? int? (p?_2 ...) Γ o_2)))
      [`(Proved Proved) (term {(((• int?) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERROR})]
      [_ (term {(((• int?) [] []) Γ ∅) ERROR})])]
  
  ; cons
  [(δ cons V_1 V_2 Γ o_1 o_2) {((V_1 V_2) Γ ∅ #|TODO could <o,o> be useful?|#)}]
  
  ; predicates
  [(δ p? ((• p?_1 ...) E O) Γ o)
   ,(match (term (Γ⊢? p? (p?_1 ...) Γ o))
      ['Proved (term {((#t [] []) (Γ:: p? o Γ) ∅)})]
      ['Refuted (term {((#f [] []) (Γ:: (¬ p?) o Γ) ∅)})]
      ['Neither (term {((#t [] []) (Γ:: p? o Γ) ∅)
                       ((#f [] []) (Γ:: (¬ p?) o Γ) ∅)})])]
  [(δ p? V Γ o)
   ,(match (term (concrete-check p? V))
      [#t (term {((#t [] []) (Γ:: p? o Γ) ∅)})]
      [#f (term {((#f [] []) (Γ:: (¬ p?) o Γ) ∅)})])]
  
  [(δ op V ... Γ o ...) {ERROR}])

;; uses existing information to check whether the predicate holds for given value
(define-metafunction oc
  Γ⊢? : p? (p? ...) Γ o -> Verified?
  [(Γ⊢? p? (any_1 ... p?_1 any_2 ...) Γ o) Proved
                                           (where #t (implies? p?_1 p?))]
  [(Γ⊢? p? any (any_1 ... [o′ ↦ (any_3 ... p?_1 any_4 ...) ψs ...] any_2 ...) o′) Proved
                                                                                  (where #t (implies? p?_1 p?))]
  [(Γ⊢? p? (any_1 ... p?_1 any_2 ...) Γ o) Refuted
                                           (where #t (excludes? p? p?_1))]
  [(Γ⊢? p? any (any_1 ... [o′ ↦ (any_3 ... p?_1 any_4 ...) ψs ...] any_2 ...) o′) Refuted
                                                                                  (where #t (excludes? p? p?_1))]
  [(Γ⊢? p? any (any_1 ... [o′ ↦ (any_3 ... (¬ p?) any_4 ...) ψs ...] any_2 ...) o′) Refuted]
  [(Γ⊢? p? any Γ o) Neither])

;; checks whether given set of predicates prevents the new one to hold
(define-metafunction oc
  excludes? : p? p? -> b
  [(excludes? p?_1 p?_2)
   ,(ormap (λ (S) (and (not (equal? (term p?_1) (term p?_2)))
                       (member (term p?_1) S)
                       (member (term p?_2) S) #t))
           `((true? false?)
             (int? str? bool? proc? cons?)))])

;; checks whether first predicates implies second
(define-metafunction oc
  implies? : p? p? -> b
  [(implies? p? p?) #t]
  [(implies? false? true?) #f]
  [(implies? p? true?) #t]
  [(implies? p?_1 p?_2) #f])

;; checks predicates on concrete values
(define-metafunction oc
  concrete-check : p? V -> b
  [(concrete-check int? (n E O)) #t]
  [(concrete-check zero? (0 E O)) #t]
  [(concrete-check str? (s E O)) #t]
  [(concrete-check false? (#f E O)) #t]
  [(concrete-check false? V) #f]
  [(concrete-check bool? (b E O)) #t]
  [(concrete-check proc? ((λ (x) e) E O)) #t]
  [(concrete-check true? (#f E O)) #f]
  [(concrete-check true? V) #t]
  [(concrete-check cons? (V_1 V_2)) #t]
  [(concrete-check p? V) #f])

;; split pair closure into 2, or () indicating not a pair
(define-metafunction oc
  split-cons : V Γ o -> {(V ...) ...} ; (V ...) being (V V) or ()
  [(split-cons (V_1 V_2) Γ o) {(V_1 V_2)}]
  [(split-cons ((• p? ...) E O) Γ o)
   ,(match (term (Γ⊢? cons? (p? ...) Γ o))
      ['Proved (term {(((•) [] []) ((•) [] []))})]
      ['Refuted (term {()})]
      ['Neither (term {(((•) [] []) ((•) [] []))
                       ()})])]
  [(split-cons V Γ o) {()}])

;; adds new binding to environment
(define-metafunction oc
  :: : (o ↦ any) ([o ↦ any] ...) -> ([o ↦ any] ...)
  [(:: (∅ ↦ any) any_1) any_1]
  [(:: (o ↦ ∅) any) any]
  [(:: (o ↦ any) (any_1 ...)) ([o ↦ any] any_1 ...)])

;; look up environment
(define-metafunction oc
  ! : o ([o ↦ any] ...) -> any
  [(! o ([o ↦ any] any_1 ...)) any]
  [(! o ([o_1 ↦ any_1] any_2 ...)) (! o (any_2 ...))]
  [(! o []) ,(error "environment does not have" (term o))])

;; returns car/cdr of the path
(define-metafunction oc
  car-o : o -> o
  [(car-o ∅) ∅]
  [(car-o o) (car o)])
(define-metafunction oc
  [(cdr-o ∅) ∅]
  [(cdr-o o) (cdr o)])

;; defaults to given non-empty path
(define-metafunction oc
  default-o : o′ o -> o′
  [(default-o o′ ∅) o′]
  [(default-o any o) o])

;; transforms program to smaller set of syntax
(define-metafunction oc
  desug : e -> e
  [(desug (λ (x) e)) (λ (x) (desug e))]
  [(desug (λ (x z ...) e)) (λ (x) (desug (λ (z ...) e)))]
  [(desug (f e)) ((desug f) (desug e))]
  [(desug (f e_1 e_2 ...)) (desug ((f e_1) e_2 ...))]
  [(desug (if e ...)) (if (desug e) ...)]
  [(desug (μ (x) e)) (μ (x) (desug e))]
  [(desug (op e ...)) (op (desug e) ...)]
  [(desug (and e)) (desug e)]
  [(desug (and e_1 e_2 ...)) (if (desug e_1) (desug (and e_2 ...)) #f)]
  [(desug (or e)) (desug e)]
  [(desug (or e_1 e_2 ...)) (desug (let [tmp e_1]
                                     (if tmp tmp (or e_2 ...))))]
  [(desug (begin e)) (desug e)]
  [(desug (begin e_1 e_2 ...)) (desug (let [_ e_1] (begin e_2 ...)))]
  [(desug (let [x e_1] e)) ((λ (x) (desug e)) (desug e_1))]
  [(desug (let ([x e_1] ...) e)) (desug ((λ (x ...) e) e_1 ...))]
  [(desug (cond [else e])) (desug e)]
  [(desug (cond (e_1 e_2) any ...)) (if (desug e_1)
                                        (desug e_2)
                                        (desug (cond any ...)))]
  [(desug •) (•)]
  [(desug (mon c e)) (mon (desug-c c) (desug e))]
  [(desug any) any])

;; defuglifies answer
(define-metafunction oc
  simplify : A -> any
  [(simplify ((V_1 V_2) Γ o)) (cons (simplify (V_1 [] ∅)) (simplify (V_2 [] ∅)))]
  [(simplify ((d E O) Γ o)) d]
  [(simplify (((• p? ...) E O) Γ o)) (• p? ...)]
  [(simplify (((λ (x ...) e) E O) Γ o)) function]
  [(simplify ERROR) ERROR])

;; adds new (empty) set of predicates for variable x that shadows old assumptions
(define-metafunction oc
  Γ-push-var : x Γ -> Γ
  [(Γ-push-var x [any_1 ... (x ↦ ψs ...) any_2 ...])
   (any_1 ... (x ↦ () ψs ...) any_2 ...)]
  [(Γ-push-var x [any ...]) [(x ↦ ()) any ...]])

;; invalidates the top assumptions for given variable
(define-metafunction oc
  Γ-pop-var : x Γ -> Γ
  [(Γ-pop-var x [any_1 ... (x ↦ ψs) any_2 ...]) (any_1 ... any_2 ...)] ; to make it nicer
  [(Γ-pop-var x [any_1 ... (x ↦ ψs_1 ψs_2 ...) any_2 ...]) [any_1 ... (x ↦ ψs_2 ...) any_2 ...]]
  [(Γ-pop-var x any) ,(error "WRONG:" (term any) (term x))])

;; updates Γ with new assumption
(define-metafunction oc
  Γ:: : ψ o Γ -> Γ
  [(Γ:: ψ ∅ Γ) Γ]
  [(Γ:: ψ o [any_1 ... (o ↦ (ψ_1 ...) ψs ...) any_2 ...])
   (any_1 ... (o ↦ (ψ ψ_1 ...) ψs ...) any_2 ...)]
  [(Γ:: ψ o (any ...)) ((o ↦ (ψ)) any ...)])

;; remdup : [Listof X] -> [Listof X]
;; remove duplicates
(define remdup (compose set->list list->set))

;; s-map : [X -> Y] [Listof X] -> [Listof Y]
;; like map, but remove duplicates
(define (s-map f xs)
  (remdup (map f xs)))

;; non-det [X -> [Listof Y]] [Listof X] -> [Listof Y]
(define (non-det f xs)
  (remdup (apply append (map f xs))))

;; abstracts away non-determinism and ERROR returning in ⇓
(define-syntax non-det:
  (syntax-rules (←)
    [(_ [V Γ o ← e] e1 e2 ...)
     (non-det
      (match-lambda
        [`(,V ,Γ ,o) (non-det: e1 e2 ...)]
        ['ERROR (term {ERROR})])
      (non-det: e))]
    [(_ e e1 e2 ...)
     (non-det
      (λ (_) (non-det: e1 e2 ...))
      e)]
    [(_ e) e]))
(define-syntax return:
  (syntax-rules ()
    [(_ e ...) (list e ...)]))



;;;;; TESTS

(define f2 (term (λ (x #|Number ∪ String|#)
                   (if (int? x) (add1 x) (str-len x)))))
(define strnum? (term (λ (x) (or (str? x) (int? x)))))
(define f11 (term (λ (p #|<⊤,⊤>|#) 
                    (if (and (int? (car p)) (int? (cdr p)))
                        13
                        42))))
(define carnum? (term (λ (x) ; assume x is a pair
                        (int? (car x)))))
(define f14 (term (λ (input #|Number ∪ String|#
                      extra #|<⊤,⊤>|#)
                    (cond
                      [(and (int? input) (int? (car extra)))
                       (+ input (car extra))]
                      [(int? (car extra))
                       (+ (str-len input) (car extra))]
                      [else 0]))))

;; example 1
(for-each
 (match-lambda
   [`(,prog → ,expected)
    (test-predicate
     (λ (answer)
       (equal? (list->set answer) (list->set expected)))
     (term (eval ,prog)))])
 
 (term
  (; example 1
   [(let [x •]
      (if (int? x) (add1 x) 0))
    → {0 (• int?)}]
   
   ; example 2
   [(,f2 (• int?))
    → {(• int?)}]
   
   [(,f2 (• str?))
    → {(• int?)}]
   
   ; example 3: language not enough, yet
   
   ; example 4
   [(let [z •]
      (if (or (int? z) (str? z)) (,f2 z) 0))
    → {0 (• int?)}]
   
   
   ; example 5
   [(let ([z •]
          [y •])
      (if (and (int? z) (str? y))
          (+ z (str-len y))
          0))
    → {0 (• int?)}]
   
   ; example 6 (unsafe)
   {(let ([z •]
          [y •])
      (if (and (int? z) (str? y))
          (add1 (str-len y))
          (str-len z)))
    → {(• int?) ERROR}}
   
   ; example 7
   [(let ([z •]
          [y •])
      (if (if (int? z) (str? y) #f)
          (+ z (str-len y))
          0))
    → {0 (• int?)}]
   
   ; example 8
   [(,strnum? •)
    → {#t #f}]
   
   [(,strnum? (• int?))
    → {#t}]
   
   [(,strnum? (• str?))
    → {#t}]
   
   ; example 9
   [(let [z •]
      (if (let [tmp (int? z)]
            (if tmp tmp (str? z)))
          (,f2 z)
          0))
    → {0 (• int?)}]
   
   ; example 10
   [(let [p (cons • •)]
      (if (int? (car p))
          (add1 (car p))
          7))
    → {7 (• int?)}]
   
   ; example 11
   [(,f11 (cons • •))
    → {13 42}]
   
   ; example 12
   [(,carnum? (cons • •))
    → {#t #f}]
   
   [(,carnum? (cons (• int?) •))
    → {#t}]
   
   ; example 13
   [(let ([z •]
          [y •])
      (cond
        [(and (int? z) (str? y)) 1]
        [(int? z) 2]
        [else 3]))
    → {1 2 3}]
   
   ; example 14 PUTTING IT ALL TOGETHER
   [(,f14 (• int?) (cons • •))
    → {0 (• int?)}]
   
   [(,f14 (• str?) (cons • •))
    → {0 (• int?)}]
   
   ; information is represented in terms of farthest possible variable so it can
   ; be retained
   [(let (l (cons • •))
      (begin
        (let (x (car l))
          (if (int? x) "ignore" (add1 "raise error")))
        ; if reach here, (car l) has to be nat
        (int? (car l))))
    → {#t ERROR}]
   
   ; example that illustrates previous problem when having 2 different variables
   ; of the same name
   [(let (x •)
      (if (int? x)
          (let (x •)
            (if (str? x)
                "x is a string" ; would be wrongly eliminated by previous bug
                "x is not a string"))
          "x is not a nat"))
    → {"x is a string" "x is not a string" "x is not a nat"}]
   
   ; blindly adding a new frame for variable can lead to imprecision (loss of info)
   ; when inner variable refers to outer one with the same name (and inner one
   ; gets updated while we could do so with outer one)
   [(let (x •)
      (if (int? x)
          (let (x x)
            (if (int? x) ; inner one uses outer one's info
                "inner x is nat"
                "this cannot happen"))
          "x is not nat"))
    → {"inner x is nat" "x is not nat"}]
   
   [(let (x •)
      (begin
        (let (x x)
          (if (int? x)
              "x is nat"
              (add1 "raise error")))
        (int? x))) ; outer one uses info from eval-ing inner one
    → {#t ERROR}]
   
   ; check for proper list
   [(let (proper-list? (μ (check)
                          (λ (l)
                            (or (false? l)
                                (and (cons? l) (check (cdr l)))))))
      (proper-list? (cons • (cons • #f))))
    → {#t}]
   )))

(test-results)