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
     (• C ...) #|value refined by (closed) contracts|#]
  
  ; path
  [o ∅ o′]
  [o′ x (car o′) (cdr o′)] ; TODO: could <o,o> be useful?
  
  ; closed value (with the exception of μx.e)
  [V (v E O)
     ((μ (x) e) E O) ; this is not a value, but i don't know how to deal with it
     ([(c ↦ (λ (x) c)) E O] V) ; monitored function
     (V V) #|pair|#]
  
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
  [C (c E O)]
  
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
  [(eval′ e) (⇓ [] [] [] e)])

;; big-step semantics
(define-metafunction oc
  ⇓ : E O Γ e -> {A ...}
  
  ; vals
  [(⇓ E O Γ d) {((d [] []) Γ ∅)}]
  [(⇓ E O Γ (• C ...)) {(((• C ...) [] []) Γ ∅)}]
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
         [if (equal? x o2) ; avoid precision loss for (let (x x) ...) cases
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
       ; TODO mon-fun
       [`(((,c1 ↦ (λ (,x) ,c2)) ,Ec ,Oc) ,Vf)
        (error "TODO")]
       [`((• ,p? ...) ,Eλ ,Oλ)
        (match (term (⊢? proc? ,p? ,Γ1 oλ))
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
  [(⇓ E O Γ (mon c e))
   ,(non-det:
     [V1 Γ1 o1 ← (term (⇓ E O Γ e))]
     (match (term (V⊢? ,V1 (c E O)))
       ['Proved (return: (term (,V1 ,Γ1 ,o1)))]
       ['Refuted (return: (term ERROR))]
       ['Neither 
        (match (term (FC c))
          [`(,pred) (non-det:
                     [`((λ (,x) ,e′) ,Eλ ,Oλ) Γ2 o2 ← (term (⇓ E O ,Γ1 ,pred))]
                     [V? Γ3 o3 ← (term (⇓ (:: [,x ↦ ,V1] ,Eλ)
                                          (:: [,x ↦ (default-o ,x ,o1)] ,Oλ)
                                          ,(if (equal? x o1)
                                               Γ2
                                               (term (Γ-push-var ,x ,Γ2)))
                                          ,e′))]
                     [`(,t? ,_E ,_O) _Γ _o ← (term (δ true? ,V? ,Γ3 ,o3))]
                     [if t?
                         (s-map
                          (λ (V2)
                            (term (,V2
                                   ,(if (equal? x o1)
                                        Γ3
                                        (term (Γ-pop-var ,x ,Γ3)))
                                   ,o1)))
                          (term (refine-V ,V1 (c E O))))
                         (return: (term ERROR))])]
          [#f (error "TODO")
              #;(match (term c)
                  [`(,c1 ↦ (λ (,x) ,c2))  #|create monitored function|#
                   (non-det:
                    [`(,t? _E _O) _Γ _o ← (term (δ proc? ,V1 ,Γ1 ,o1))]
                    (return: (if t? (term ((c E O) ,Γ1 ,o1)) (term ERROR))))]
                  [`(or/c ,c1 ,c2)
                   (match (term (FC ,c1))
                     [`(,p1) ; unroll it here cos grammar is not enough to express
                      (non-det:
                       [`((λ (,x) ,e′) ,Et ,Ot) Γt ot ← (term (⇓ E O ,Γ1 ,p1))]
                       [V? Γ? o? ← (term (⇓ (:: [,x ↦ ,V1] ,Et)
                                            (:: [,x ↦ (default-o ,x ,o1)] ,Ot)
                                            ,(if (equal? x o1)
                                                 Γt
                                                 (term (Γ-push-var ,x ,Γt)))
                                            ,e′))]
                       [`(,t? ,_E ,_O) _Γ _o ← (term (δ true? ,V? ,Γ? ,o?))]
                       [let ([Γ3 (if (equal? x o1) Γ? (term (Γ-pop-var ,x ,Γ?)))])
                         [if t?
                             (s-map
                              (λ (V2) (term (,V2 ,Γ3 ,o1)))
                              (term (refine-V ,V1 (,c1 E O))))
                             (term (⇓ E O ,Γ3 (mon ,c2 ,V1)))]])]
                     [#f (return: (term ERROR)) #|first disjunct has to be 1st order|#])]
                  [`(and/c ,c1 ,c2) (term (⇓ E O (mon ,c2 (mon ,c1 e))))] ; FIXME: repeated computation!
                  [`(cons/c ,c1 ,c2)
                   (non-det:
                    [`(,t? _E _O) _Γ _o ← (term (δ cons? ,V1 ,Γ1 ,o1))]
                    (if t? ; FIXME: repeated computation!
                        (term (⇓ E O ,Γ1 (cons (mon ,c1 e) (mon ,c2 e))))
                        (term {ERROR})))]
                  [`(μ (,x) ,c) (error "TODO")]
                  [`(,x) (error "TODO")]
                  [`(,c1 ↦ ,c2) (let ([z (variable-not-in (term (c1 c2)) 'x)])
                                  (non-det:
                                   [`(,t? _E _O) _Γ _o ← (term (δ proc? ,V1 ,Γ1 ,o1))]
                                   (return: (if t? (term (((,c1 ↦ (λ (,z) ,c2)) E O) ,Γ1 ,o1)) (term ERROR)))))])])]))]
  
  
  ; δ
  [(⇓ E O Γ (op1 e))
   ,(non-det:
     [V1 Γ1 o1 ← (term (⇓ E O Γ e))]
     [term (δ op1 ,V1 ,Γ1 ,o1)])]
  [(⇓ E O Γ (op2 e_1 e_2))
   ,(non-det:
     [V1 Γ1 o1 ← (term (⇓ E O Γ e_1))]
     [V2 Γ2 o2 ← (term (⇓ E O ,Γ1 e_2))]
     [term (δ op2 ,V1 ,V2 ,Γ2 ,o1 ,o2)])]
  
  ; syntactic sugar
  [(⇓ E O Γ (e_1 e_2 e_3 ...)) (⇓ E O Γ ((e_1 e_2) e_3 ...))]
  [(⇓ E O Γ (λ (x z ...) e)) (⇓ E O Γ (λ (x) (λ (z ...) e)))]
  [(⇓ E O Γ •) (⇓ E O Γ (•))]
  [(⇓ E O Γ (and e)) (⇓ E O Γ e)]
  [(⇓ E O Γ (and e_1 e_2 ...)) (⇓ E O Γ (if e_1 (and e_2 ...) #f))]
  [(⇓ E O Γ (or e)) (⇓ E O Γ e)]
  [(⇓ E O Γ (or e_1 e_2 ...)) (⇓ E O Γ (let (tmp e_1)
                                         (if tmp tmp (or e_2 ...))))]
  [(⇓ E O Γ (begin e)) (⇓ E O Γ e)]
  [(⇓ E O Γ (begin e_1 e_2 ...)) (⇓ E O Γ (let (_ e_1) (begin e_2 ...)))]
  [(⇓ E O Γ (let [x e_1] e)) (⇓ E O Γ ((λ (x) e) e_1))]
  [(⇓ E O Γ (let ([x_1 e_1]) e)) (⇓ E O Γ (let [x_1 e_1] e))]
  [(⇓ E O Γ (let ([x_1 e_1] [x_2 e_2] ...) e))
   (⇓ E O Γ (let [x_1 e_1] (let ([x_2 e_2] ...) e)))]
  [(⇓ E O Γ (cond [else e])) (⇓ E O Γ e)]
  [(⇓ E O Γ (cond [e_1 e_2] any ...)) (⇓ E O Γ (if e_1 e_2 (cond any ...)))])

;; applies primitive ops, returns result + new propositions + path object
(define-metafunction oc
  δ : op V ... Γ o ... -> {A ...}
  
  ; add1
  [(δ add1 (n E O) Γ o) {((,(add1 (term n)) [] []) Γ ∅)}]
  [(δ add1 ((• C ...) E O) Γ o)
   ,(match (term (⊢? int? (C ...) Γ o))
      ['Proved (term {(((• (mk-C int?)) [] []) Γ ∅)})]
      ['Refuted (term {ERROR})]
      ['Neither (term {(((• (mk-C int?)) [] []) (Γ:: int? o Γ) ∅)
                       ERROR})])]
  [(δ add1 V Γ o) {ERROR}]
  
  ; sub1
  [(δ sub1 (n E O) Γ o) {((,(sub1 (term n)) [] []) Γ ∅)}]
  [(δ sub1 ((• C ...) E O) Γ o)
   ,(match (term (⊢? int? (C ...) Γ o))
      ['Proved (term {(((• (mk-C int?)) [] []) Γ ∅)})]
      ['Refuted (term {ERROR})]
      ['Neither (term {(((• (mk-C int?)) [] []) (Γ:: int? o Γ) ∅)
                       ERROR})])]
  [(δ sub1 V Γ o) {ERROR}]
  
  ; str-len
  [(δ str-len (s E O) Γ o) {((,(string-length (term s)) [] []) Γ o)}]
  [(δ str-len ((• C ...) E O) Γ o)
   ,(match (term (⊢? str? (C ...) Γ o))
      ['Proved (term {(((• (mk-C int?)) [] []) Γ ∅)})]
      ['Refuted (term {ERROR})]
      ['Neither (term {(((• (mk-C int?)) [] []) (Γ:: str? o Γ) ∅)
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
  [(δ + ((• C ...) E_1 O_1) (n E_2 O_2) Γ o_1 o_2)
   (δ + ((• C ...) [] []) ((• (mk-C int?)) [] []) Γ o_1 o_2)]
  [(δ + (m E_1 O_1) ((• C ...) E_2 O_2) Γ o_1 o_2)
   (δ + ((• (mk-C int?)) [] []) ((• C ...) [] []) Γ o_1 o_2)]
  [(δ + ((• C_1 ...) E_1 O_1) ((• C_2 ...) E_2 O_2) Γ o_1 o_2)
   ,(match (term ((⊢? int? (C_1 ...) Γ o_1) (⊢? int? (C_2 ...) Γ o_2)))
      [`(Proved Proved) (term {(((• (mk-C int?)) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERROR})]
      [_ (term {(((• (mk-C int?)) [] []) Γ ∅) ERROR})])]
  
  ; -
  [(δ - (m [] []) (n [] []) Γ o_1 o_2)
   {((,(- (term m) (term n)) [] []) Γ ∅)}]
  [(δ - ((• C ...) E_1 O_1) (n E_2 O_2) Γ o_1 o_2)
   (δ - ((• C ...) [] []) ((• (mk-C int?)) [] []) Γ o_1 o_2)]
  [(δ - (m E_1 O_1) ((• C ...) E_2 O_2) Γ o_1 o_2)
   (δ - ((• (mk-C int?)) [] []) ((• C ...) [] []) Γ o_1 o_2)]
  [(δ - ((• C_1 ...) E_1 O_1) ((• C_2 ...) E_2 O_2) Γ o_1 o_2)
   ,(match (term ((⊢? int? (C_1 ...) Γ o_1) (⊢? int? (C_2 ...) Γ o_2)))
      [`(Proved Proved) (term {(((• (mk-C int?)) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERROR})]
      [_ (term {(((• (mk-C int?)) [] []) Γ ∅) ERROR})])]
  
  ; *
  [(δ * (m [] []) (n [] []) Γ o_1 o_2)
   {((,(* (term m) (term n)) [] []) Γ ∅)}]
  [(δ * ((• C ...) E_1 O_1) (n E_2 O_2) Γ o_1 o_2)
   (δ * ((• C ...) [] []) ((• (mk-C int?)) [] []) Γ o_1 o_2)]
  [(δ * (m E_1 O_1) ((• C ...) E_2 O_2) Γ o_1 o_2)
   (δ * ((• (mk-C int?)) [] []) ((• C ...) [] []) Γ o_1 o_2)]
  [(δ * ((• C_1 ...) E_1 O_1) ((• C_2 ...) E_2 O_2) Γ o_1 o_2)
   ,(match (term ((⊢? int? (C_1 ...) Γ o_1) (⊢? int? (C_2 ...) Γ o_2)))
      [`(Proved Proved) (term {(((• (mk-C int?)) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERROR})]
      [_ (term {(((• (mk-C int?)) [] []) Γ ∅) ERROR})])]
  
  ; cons
  [(δ cons V_1 V_2 Γ o_1 o_2) {((V_1 V_2) Γ ∅ #|TODO could <o,o> be useful?|#)}]
  
  ; predicates
  [(δ p? ((• C_1 ...) E O) Γ o)
   ,(match (term (⊢? p? (C_1 ...) Γ o))
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
  ⊢? : p? (C ...) Γ o -> Verified?
  ; Γ is easier/cheaper, so use it first
  [(⊢? p? (C ...) Γ o) ,(match (term (Γ⊢? p? Γ o))
                          ['Proved (term Proved)]
                          ['Refuted (term Refuted)]
                          ['Neither (term (C⊢? p? (C ...)))])])

;; checks whether proposition set can prove predicate
(define-metafunction oc
  Γ⊢? : p? Γ o -> Verified?
  [(Γ⊢? p? (any_1 ... [o′ ↦ (any_3 ... p?_1 any_4 ...) ψs ...] any_2 ...) o′)
   Proved
   (where #t (implies? p?_1 p?))]
  [(Γ⊢? p? (any_1 ... [o′ ↦ (any_3 ... p?_1 any_4 ...) ψs ...] any_2 ...) o′)
   Refuted
   (where #t (excludes? p? p?_1))]
  [(Γ⊢? p? (any_1 ... [o′ ↦ (any_3 ... (¬ p?_1) any_4 ...) ψs ...] any_2 ...) o′)
   Refuted
   (where #t (implies? p? p?_1))]
  [(Γ⊢? any_p? any_Γ any_o) Neither])

;; checks whether contract set can prove predicate
(define-metafunction oc
  C⊢? : p? (C ...) -> Verified?
  [(C⊢? p? (any_1 ... ((flat (λ (x) (p?_1 x))) E O) any_2 ...))
   Proved
   (where #t (implies? p?_1 p?))]
  [(C⊢? p? (any_1 ... ((flat (λ (x) (p?_1 x))) E O) any_2 ...))
   Refuted
   (where #t (excludes? p? p?_1))]
  [(C⊢? p? (C ...)) Neither])

;; checks whether value satisfies contract
(define-metafunction oc
  V⊢? : V C -> Verified?
  [(V⊢? ((• any_1 ... C_1 any_2 ...) E_1 O_1) C_2)
   Proved
   (where #t (C-implies? C_1 C_2))]
  [(V⊢? ((• any_1 ... C_1 any_2 ...) E_1 O_1) C_2)
   Refuted
   (where #t (C-excludes? C_1 C_2))]
  [(V⊢? V C) Neither])

;; checks whether first contract is *sure* to imply second one
;; may return false negative
(define-metafunction oc
  C-implies? : C C -> b
  [(C-implies? ((flat (λ (x) (p?_1 x))) E_1 O_1)
               ((flat (λ (z) (p?_2 z))) E_2 O_2))
   (implies? p?_1 p?_2)]
  [(C-implies? C_1 C_2) #f])

;; checks whether first contract is *sure* to exclude second one
;; may return false negative
(define-metafunction oc
  C-excludes? : C C -> b
  [(C-excludes? ((flat (λ (x) (p?_1 x))) E_1 O_1)
                ((flat (λ (z) (p?_2 z))) E_2 O_2))
   (excludes? p?_1 p?_2)]
  [(C-excludes? C_1 C_2) #f])

;; flattens flat contract into expression, or #f for higher-order contracts
(define-metafunction oc
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
   ,(match (term (⊢? cons? (p? ...) Γ o))
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

;; defuglifies answer
(define-metafunction oc
  simplify : A -> any
  [(simplify ((V_1 V_2) Γ o)) (cons (simplify (V_1 [] ∅)) (simplify (V_2 [] ∅)))]
  [(simplify ((d E O) Γ o)) d]
  [(simplify (((• C ...) E O) Γ o))
   ,(match (term (all-preds (C ...) Γ o))
      ['() (term •)]
      [ps (term (• ,@ ps))])]
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

;; makes closed contract out of primitive predicate
(define-metafunction oc
  mk-C : p? -> C
  [(mk-C p?) ((flat (λ (x) (p? x))) [] [])])

(define-metafunction oc
  c-η-sim : any -> any
  [(c-η-sim (λ (x) (any x))) (c-η-sim any)]
  [(c-η-sim (flat any)) (c-η-sim any)]
  [(c-η-sim any) any])

;; refines set of contracts
(define-metafunction oc
  refine : {C ...} C -> {{C ...} ...}
  
  ; special cases where there's something we can do
  [(refine {any_1 ... C_1 any_2 ...} C_2)
   {any_1 ... C_1 any_2 ...}
   (where #t (C-implies? C_1 C_2))]
  [(refine {any_1 ... C_1 any_2 ...} C_2)
   {any_1 ... C_2 any_2 ...}
   (where #t (C-implies? C_2 C_1))]
  [(refine {any_1 ... C_1 any_2 ...} C_2)
   {}
   (where #t (C-excludes? C_1 C_2))]
  
  ; generic ones...
  [(refine {C ...} ((or/c c_1 c_2) E O))
   ,(∪ (term (refine {C ...} (c_1 E O)))
       (term (refine {C ...} (c_2 E O))))]
  [(refine {C ...} ((and/c c_1 c_2) E O))
   ,(s-map
     (λ (Cs)
       (term (refine ,Cs (c_2 E O))))
     (term (refine {C ...} (c_2 E O))))]
  [(refine {C ...} ((μ (x) c) E O))
   (refine {C ...} (c (:: [x ↦ ((μ (x) c) E O)] E)
                      (:: [x ↦ x] O)))]
  [(refine {C ...} C_1) {{C_1 C ...}}])

;; refines value
(define-metafunction oc
  refine-V : V C -> {V ...}
  [(refine-V ((• C_1 ...) E O) C)
   ,(s-map
     (λ (Cs)
       (term ((• ,@ Cs) [] [])))
     (term (refine (C_1 ...) C)))]
  [(refine-V V C) {V}])

;; returns all possible predicates for displaying
(define-metafunction oc
  all-preds : (C ...) Γ o -> (ψ ...)
  [(all-preds (C ...) Γ o) ,(∪ (term (C-all-preds C ...))
                               (term (Γ-all-preds Γ o)))])
(define-metafunction oc
  C-all-preds : C ... -> (p? ...)
  [(C-all-preds (c E O) ...) ((c-η-sim c) ...)])
(define-metafunction oc
  Γ-all-preds : Γ o -> (p? ...)
  [(Γ-all-preds (any_1 ... [o′ ↦ ψs ψs_1 ...] any_2 ...) o′)
   (p? ...)
   (where (p? ...) (remove-negs ψs))]
  [(Γ-all-preds any any_1) {}])
(define-metafunction oc
  remove-negs : ψs -> (p? ...)
  [(remove-negs {}) {}]
  [(remove-negs (p? ψ ...)) ,(cons (term p?) (term (remove-negs (ψ ...))))]
  [(remove-negs ((¬ p?) ψ ...)) (remove-negs (ψ ...))])

;; remdup : [Listof X] -> [Listof X]
;; remove duplicates
(define remdup (compose set->list list->set))

;; ∪ : [Listof Any] [Listof Any] -> [Listof Any]
(define (∪ xs ys)
  (remdup (append xs ys)))

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

(define c/int (term ((flat (λ (x) (int? x))) [] [])))
(define c/str (term ((flat (λ (x) (str? x))) [] [])))

;; example 1
(for-each
 (match-lambda
   [`(,prog → ,expected)
    (test-equal (list->set (term (eval ,prog)))
                (list->set expected))])
 
 (term
  (; example 1
   [(let [x •]
      (if (int? x) (add1 x) 0))
    → {0 (• int?)}]
   
   ; example 2
   [(,f2 (• ,c/int))
    → {(• int?)}]
   
   [(,f2 (• ,c/str))
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
   
   [(,strnum? (• ,c/int))
    → {#t}]
   
   [(,strnum? (• ,c/str))
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
   
   [(,carnum? (cons (• ,c/int) •))
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
   [(,f14 (• ,c/int) (cons • •))
    → {0 (• int?)}]
   
   [(,f14 (• ,c/str) (cons • •))
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
        (int? x))) ; outer x uses info from eval-ing inner x
    → {#t ERROR}]
   
   ; with contracts
   [(mon (flat (λ (x) (int? x))) •)
    → {ERROR (• int?)}]
   [(mon (flat (λ (x) (int? x))) (• ,c/str))
    → {ERROR}]
   [(mon (flat (λ (x) (int? x))) (• ,c/int))
    → {(• int?)}]
   
   ; check for proper list
   [(let (proper-list? (μ (check)
                          (λ (l)
                            (or (false? l)
                                (and (cons? l) (check (cdr l)))))))
      (proper-list? (cons • (cons • #f))))
    → {#t}]
   
   ; 'lastpair' from Wright paper (with a safe counter to make sure it terminates)
   [(let [lastpair (μ (lp)
                      (λ (s n)
                        (cond
                          [(zero? n) "killed"]
                          [(cons? (cdr s)) (lp (cdr s) (sub1 n))]
                          [else s])))]
      (lastpair (cons • •) 5))
    → {"killed" (• cons?) (cons • •)}])))
(test-results)