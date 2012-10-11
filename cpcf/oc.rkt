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
            
            ; syntactic sugar
            (and e e ...)
            (or e e ...)
            (begin e e ...)
            (let [x e] e)
            (let ([x e] [x e] ...) e)
            (cond [e e] ... [else e])]
  
  ; value
  [v c
     (λ (x x ...) e)
     (• p? ...) #|value refined by predicates|#]
  
  ; path
  [o ∅ o′]
  [o′ x (car o′) (cdr o′)] ; TODO: could <o,o> be useful?
  
  ; closed value
  [V (v E O)
     (V V)]
  
  ; environments
  [E ([x ↦ V] ...)]
  [O ([x ↦ o′] ...)]
  [Γ ([o′ ↦ ψ] ...)]
  
  ; predicate
  [ψ p? (¬ p?)]
  
  ; evaluation answer
  [A (V Γ o)
     ERROR]
  
  ; verification answer
  [Verified? Proved Refuted Neither]
  
  [op1 p? add1 str-len car cdr]
  [op2 + cons]
  [op op1 op2]
  [p? nat? str? cons? true? false? bool? proc?]
  [c b n s]
  [(m n) natural]
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
  [(⇓ E O Γ c) {((c [] []) Γ ∅)}]
  [(⇓ E O Γ (• p? ...)) {(((• p? ...) [] []) Γ ∅)}]
  [(⇓ E O Γ (λ (x) e)) {(((λ (x) e) E O) Γ ∅)}]
  
  ; var
  [(⇓ E O Γ x) {((! x E) Γ (! x O))}]
  
  ; app
  [(⇓ E O Γ (f e))
   ,(non-det
     (match-lambda
       [`(((λ (,x) ,e′) ,Eλ ,Oλ) ,Γ1 ,o1)
        (non-det
         (match-lambda
           [`(,V ,Γ2 ,o2)
            (term (⇓ (:: [,x ↦ ,V] ,Eλ) (:: [,x ↦ (default-o ,x ,o2)] ,Oλ) ,Γ2 ,e′))]
           ['ERROR (term {ERROR})])
         (term (⇓ E O ,Γ1 e)))]
       [`(((• ,p? ...) ,Eλ ,Oλ) ,Γ1 ,o1)
        (match (term (Γ⊢? proc? ,p? ,Γ1 ,o1))
          ['Refuted (term {ERROR})]
          [(or 'Proved 'Neither) (term {(((•) [] []) ,Γ1 ∅)
                                        ERROR})])]
       ['ERROR (term {ERROR})])
     (term (⇓ E O Γ f)))]
  
  ; if
  [(⇓ E O Γ (if e_1 e_2 e_3))
   ,(non-det
     (match-lambda
       [`(,V1 ,Γ1 ,o1)
        (non-det
         (match-lambda
           [`((#t [] []) ,Γ2 ,o2) (term (⇓ E O ,Γ1 e_2))]
           [`((#f [] []) ,Γ2 ,o2) (term (⇓ E O ,Γ1 e_3))])
         (term (δ true? ,V1 ,Γ1 ,o1)))]
       ['ERROR (term {ERROR})])
     (term (⇓ E O Γ e_1)))]
  
  ; δ
  [(⇓ E O Γ (op1 e))
   ,(non-det
     (match-lambda
       [`(,V ,Γ1 ,o1) (term (δ op1 ,V ,Γ1 ,o1))]
       ['ERROR (term {ERROR})])
     (term (⇓ E O Γ e)))]
  
  [(⇓ E O Γ (op2 e_1 e_2))
   ,(non-det
     (match-lambda
       [`(,V1 ,Γ1 ,o1)
        (non-det
         (match-lambda
           [`(,V2 ,Γ2 ,o2) (term (δ op2 ,V1 ,V2 ,Γ2 ,o1 ,o2))]
           ['ERROR (term {ERROR})])
         (term (⇓ E O ,Γ1 e_2)))]
       ['ERROR (term {ERROR})])
     (term (⇓ E O Γ e_1)))])


;; applies primitive ops, returns result + new propositions + path object
(define-metafunction oc
  δ : op V ... Γ o ... -> {A ...}
  
  ; add1
  [(δ add1 (n E O) Γ o) {((,(add1 (term n)) [] []) Γ ∅)}]
  [(δ add1 ((• p? ...) E O) Γ o)
   ,(match (term (Γ⊢? nat? (p? ...) Γ o))
      ['Proved (term {(((• nat?) [] []) Γ ∅)})]
      ['Refuted (term {ERROR})]
      ['Neither (term {(((• nat?) [] []) (:: (o ↦ nat?) Γ) ∅)
                       ERROR})])]
  [(δ add1 V Γ o) {ERROR}]
  
  ; str-len
  [(δ str-len (s E O) Γ o) {((,(string-length (term s)) [] []) Γ o)}]
  [(δ str-len ((• p? ...) E O) Γ o)
   ,(match (term (Γ⊢? str? (p? ...) Γ o))
      ['Proved (term {(((• nat?) [] []) Γ o)})]
      ['Refuted (term {ERROR})]
      ['Neither (term {(((• nat?) [] []) (:: (o ↦ str?) Γ) ∅)
                       ERROR})])]
  [(δ str-len V Γ o) {ERROR}]
  
  ; car, cdr
  [(δ car V Γ o)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V1 (:: (o ↦ cons?) Γ) (car-o o)))]
       [`() (term ERROR)])
     (term (split-cons V Γ o)))]
  [(δ cdr V Γ o)
   ,(s-map
     (match-lambda
       [`(,V1 ,V2) (term (,V2 (:: (o ↦ cons?) Γ) (cdr-o o)))]
       [`() (term ERROR)])
     (term (split-cons V Γ o)))]
  
  ; +
  [(δ + (m [] []) (n [] []) Γ o_1 o_2)
   {((,(+ (term m) (term n)) [] []) Γ ∅)}]
  [(δ + ((• p? ...) E_1 O_1) (n E_2 O_2) Γ o_1 o_2)
   (δ + ((• p? ...) [] []) ((• nat?) [] []) Γ o_1 o_2)]
  [(δ + (m E_1 O_1) ((• p? ...) E_2 O_2) Γ o_1 o_2)
   (δ + ((• nat?) [] []) ((• p? ...) [] []) Γ o_1 o_2)]
  [(δ + ((• p?_1 ...) E_1 O_1) ((• p?_2 ...) E_2 O_2) Γ o_1 o_2)
   ,(match (term ((Γ⊢? nat? (p?_1 ...) Γ o_1) (Γ⊢? nat? (p?_2 ...) Γ o_2)))
      [`(Proved Proved) (term {(((• nat?) [] []) Γ ∅)})]
      [(or `(Refuted ,_) `(,_ Refuted)) (term {ERROR})]
      [_ (term {(((• nat?) [] []) Γ ∅) ERROR})])]
  
  ; cons
  [(δ cons V_1 V_2 Γ o_1 o_2) {((V_1 V_2) Γ ∅ #|TODO could <o,o> be useful?|#)}]
  
  ; predicates
  [(δ p? ((• p?_1 ...) E O) Γ o)
   ,(match (term (Γ⊢? p? (p?_1 ...) Γ o))
      ['Proved (term {((#t [] []) (:: (o ↦ p?) Γ) ∅)})]
      ['Refuted (term {((#f [] []) (:: (o ↦ (¬ p?)) Γ) ∅)})]
      ['Neither (term {((#t [] []) (:: (o ↦ p?) Γ) ∅)
                       ((#f [] []) (:: (o ↦ (¬ p?)) Γ) ∅)})])]
  [(δ p? V Γ o)
   ,(match (term (concrete-check p? V))
      [#t (term {((#t [] []) (:: (o ↦ p?) Γ) ∅)})]
      [#f (term {((#f [] []) (:: (o ↦ (¬ p?)) Γ) ∅)})])])

;; uses existing information to check whether the predicate holds for given value
(define-metafunction oc
  Γ⊢? : p? (p? ...) Γ o -> Verified?
  [(Γ⊢? p? (any_1 ... p?_1 any_2 ...) Γ o) Proved
     (where #t (implies? p?_1 p?))]
  [(Γ⊢? p? any (any_1 ... [o′ ↦ p?_1] any_2 ...) o′) Proved
     (where #t (implies? p?_1 p?))]
  [(Γ⊢? p? (any_1 ... p?_1 any_2 ...) Γ o) Refuted
     (where #t (excludes? p? p?_1))]
  [(Γ⊢? p? any (any_1 ... [o′ ↦ p?_1] any_2 ...) o′) Refuted
     (where #t (excludes? p? p?_1))]
  [(Γ⊢? p? any (any_1 ... [o′ ↦ (¬ p?)] any_2 ...) o′) Refuted]
  [(Γ⊢? p? any Γ o) Neither])

;; checks whether given set of predicates prevents the new one to hold
(define-metafunction oc
  excludes? : p? p? -> b
  [(excludes? p?_1 p?_2)
   ,(ormap (λ (S) (and (not (equal? (term p?_1) (term p?_2)))
                       (member (term p?_1) S)
                       (member (term p?_2) S) #t))
           `((true? false?)
             (nat? str? bool? proc? cons?)))])

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
  [(concrete-check nat? (n E O)) #t]
  [(concrete-check str? (s E O)) #t]
  [(concrete-check false? (#f E O)) #t]
  [(concrete-check false? V) #f]
  [(concrete-check bool? (b E O)) #t]
  [(concrete-check proc? ((λ (x) e) E O)) #t]
  [(concrete-check true? (#f E O)) #f]
  [(concrete-check true? V) #t]
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
  [(desug (cons e ...)) (cons (desug e) ...)]
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
  [(desug any) any])

;; defuglifies answer
(define-metafunction oc
  simplify : A -> any
  [(simplify ((V_1 V_2) Γ o)) (cons (simplify (V_1 [] ∅)) (simplify (V_2 [] ∅)))]
  [(simplify ((c E O) Γ o)) c]
  [(simplify (((• p? ...) E O) Γ o)) (• p? ...)]
  [(simplify (((λ (x ...) e) E O) Γ o)) function]
  [(simplify ERROR) ERROR])

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


;;;;; TESTS

(define f2 (term (λ (x #|Number ∪ String|#)
                   (if (nat? x) (add1 x) (str-len x)))))
(define strnum? (term (λ (x) (or (str? x) (nat? x)))))
(define f11 (term (λ (p #|<⊤,⊤>|#) 
                    (if (and (nat? (car p)) (nat? (cdr p)))
                        13
                        42))))
(define carnum? (term (λ (x) ; assume x is a pair
                        (nat? (car x)))))
(define f14 (term (λ (input #|Number ∪ String|#
                      extra #|<⊤,⊤>|#)
                    (cond
                      [(and (nat? input) (nat? (car extra)))
                       (+ input (car extra))]
                      [(nat? (car extra))
                       (+ (str-len input) (car extra))]
                      [else 0]))))

;; example 1
(for-each
 (λ (t) ; i don't know anything about formatting
   (print t)
   (display "\n → ")
   (print (term (eval ,t)))
   (display "\n\n"))
 
 (term
  (; example 1
   (let [x (•)]
     (if (nat? x) (add1 x) 0))
   
   ; example 2
   (,f2 (• nat?))
   (,f2 (• str?))
   
   ; example 3: language not enough, yet
   
   ; example 4
   (let [z (•)]
     (if (or (nat? z) (str? z)) (,f2 z) 0))
   
   ; example 5
   (let ([z (•)]
         [y (•)])
     (if (and (nat? z) (str? y))
         (+ z (str-len y))
         0))
   
   ; example 6 (unsafe)
   (let ([z (•)]
         [y (•)])
     (if (and (nat? z) (str? y))
         (add1 (str-len y))
         (str-len z)))
   
   ; example 7
   (let ([z (•)]
         [y (•)])
     (if (if (nat? z) (str? y) #f)
         (+ z (str-len y))
         0))
   
   ; example 8
   (,strnum? (•))
   (,strnum? (• nat?))
   (,strnum? (• str?))
   
   ; example 9
   (let [z (•)]
     (if (let [tmp (nat? z)]
           (if tmp tmp (str? z)))
         (,f2 z)
         0))
   
   ; example 10
   (let [p (cons (•) (•))] ; i swear i didn't intend to make it look like this
     (if (nat? (car p))
         (add1 (car p))
         7))
   
   ; example 11
   (,f11 (cons (•) (•)))
   
   ; example 12
   (,carnum? (cons (•) (•)))
   (,carnum? (cons (• nat?) (•)))
   
   ; example 13
   (let ([z (•)]
         [y (•)])
     (cond
       [(and (nat? z) (str? y)) 1]
       [(nat? z) 2]
       [else 3]))
   
   ; example 14 PUTTING IT ALL TOGETHER
   (,f14 (• nat?) (cons (•) (•)))
   (,f14 (• str?) (cons (•) (•))))))

