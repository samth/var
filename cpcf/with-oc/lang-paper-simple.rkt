#lang racket
(require redex)

(provide
 λrec ⇓ APP δ proves? close A→EA ev ! :: render-⇓ render-APP rewrite-:: rewrite-!)

(define-language λrec
  ; expression
  [e a x (e e e ...) (if e e e)]
  [a err v]
  [v (λ x e) #;(rec (f x) e) b]
  [b n #t #f s o]
  [o o1 o2]
  [o1 p? car cdr add1 sub1 str-len]
  [o2 cons + - * /]
  [(m n) number]
  [s string]
  [p? num? str? true? false? cons? proc? zero?]
  [acc car cdr]
  
  [+|-|* + - * /]
  [add/sub1 add1 sub1]
  
  ; environment
  [ρ ([x ↦ V] ...)]
  
  ; closure
  [V ((λ x e) ρ) ((rec (f x) e) ρ) b (Cons V V)]
  [A V ERR]
  [PROC ((λ x e) ρ) ((rec (f x) e) ρ) o]
  [(f x y z) variable-not-otherwise-mentioned]
  
  [Verified? Proved Refuted Neither]
  
  [EA b function ERR (Cons EA EA)])

(define-judgment-form λrec
  #:mode     (⇓ I I O)
  #:contract (⇓ ρ e A)
  [----- "err"
   (⇓ ρ err ERR)]
  [----- "val"
   (⇓ ρ v [close v ρ])]
  [----- "var"
   (⇓ ρ x [! ρ x])]
  [(⇓ ρ e_f V_f)
   (⇓ ρ e_x V_x) ...
   ----- "app"
   (⇓ ρ (e_f e_x ...) [APP V_f [V_x ...]])]
  [(⇓ ρ e_1 V_1) ...
   (⇓ ρ e_i Err)
   ----- "app-err"
   (⇓ ρ (e_1 ... e_i e_i+1 ...) ERR)]
  
  [(⇓ ρ e V_t)
   (where #f (δ false? V_t))
   (⇓ ρ e_1 A)
   ----- "if-true"
   (⇓ ρ (if e e_1 e_2) A)]
  [(⇓ ρ e V_t)
   (where #t (δ false? V_t))
   (⇓ ρ e_2 A)
   ----- "if-false"
   (⇓ ρ (if e e_1 e_2) A)]
  [(⇓ ρ e ERR)
   ----- "if-err"
   (⇓ ρ (if e e_1 e_2) ERR)])

(define-metafunction λrec
  APP : V [V ...] -> A
  [(APP ((λ x e) ρ) [V])
   A
   (where (A) ,(judgment-holds (⇓ [:: ρ [x ↦ V]] e A) A))]
  #;[(APP ((rec (f x) e) ρ) [V])
   A
   (where (A) ,(judgment-holds (⇓ [:: ρ [f ↦ ((rec (f x) e) ρ)] [x ↦ V]] e A) A))]
  [(APP o [V ...]) (δ o V ...)]
  [(APP any any_1) ERR])

(define-metafunction λrec
  δ : o V ... -> A
  [(δ p? V)
   #t
   (where Proved (proves? V p?))]
  [(δ p? V)
   #f
   (where Refuted (proves? V p?))]
  [(δ add1 n) ,(add1 (term n))]
  [(δ sub1 n) ,(sub1 (term n))]
  [(δ + m n) ,(+ (term m) (term n))]
  [(δ - m n) ,(- (term m) (term n))]
  [(δ * m n) ,(* (term m) (term n))]
  [(δ / m 0) ERR]
  [(δ / m n) ,(/ (term m) (term n))]
  [(δ cons V_1 V_2) (Cons V_1 V_2)]
  [(δ car (Cons V_1 V_2)) V_1]
  [(δ cdr (Cons V_1 V_2)) V_2]
  [(δ str-len s) ,(string-length (term s))]
  [(δ o V ...) ERR])

(define-metafunction λrec
  close : v ρ -> V
  [(close b ρ) b]
  [(close (λ x e) ρ) ((λ x e) ρ)]
  [(close (rec (f x) e) ρ) ((rec (f x) e) ρ)])

(define-metafunction λrec
  proves? : V p? -> Verified?
  [(proves? 0 zero?) Proved]
  [(proves? n num?) Proved]
  [(proves? s str?) Proved]
  [(proves? #f false?) Proved]
  [(proves? #t true?) Proved]
  [(proves? (Cons V_1 V_2) cons?) Proved]
  [(proves? PROC proc?) Proved]
  [(proves? V p?) Refuted])

(define-metafunction λrec
  :: : ([any ↦ any] ...) (any ↦ any) ... -> ([any ↦ any] ...)
  [(:: any) any]
  [(:: (any_1 ... [any_k ↦ any_v] any_i ...) (any_k ↦ any_u) any ...)
   (:: (any_1 ... [any_k ↦ any_u] any_i ...) any ...)]
  [(:: (any_1 ...) [any_k ↦ any_v] any ...)
   (:: ([any_k ↦ any_v] any_1 ...) any ...)])

(define-metafunction λrec
  ! : ([any ↦ any] ...) any -> any
  [(! (any_1 ... [any_k ↦ any_v] any_i ...) any_k) any_v])

(define-metafunction λrec
  A→EA : A -> EA
  [(A→EA ERR) ERR]
  [(A→EA b) b]
  [(A→EA PROC) function]
  [(A→EA (Cons V_1 V_2)) (Cons (A→EA V_1) (A→EA V_2))])

(define-metafunction λrec
  ev : e -> A
  [(ev e) A (where (A) ,(judgment-holds (⇓ () e A) A))])

(define rewrite-⇓
  (match-lambda
    [`(,_ ,_ ,ρ ,e ,A ,_) `(,ρ " ⊢ " ,e " ⇓ " ,A)]))

(define rewrite-!
  (match-lambda
    [`(,_ ,_ ,ρ ,x ,_) `(,ρ "[" ,x "]")]))
  
(define (render-⇓
         [cs '("err" "val" "var" "app" "app-err" "if-true" "if-false" "if-err")])
  (with-compound-rewriters
   (['⇓ rewrite-⇓] ['! rewrite-!] [':: rewrite-::])
   (parameterize ([judgment-form-cases cs])
     (render-judgment-form ⇓))))

(define rewrite-::
  (match-lambda
    [`(,_ ,_ ,ρ ,_) `(,ρ)]
    [`(,_ ,_ ,ρ ,p1 ,_) `(,ρ "," ,p1)]
    [`(,_ ,_ ,ρ ,p1 ,p2 ,_) `(,ρ "/" ,p1 "/" ,p2)]))

(define (render-APP)
  (with-compound-rewriters
   (['⇓ rewrite-⇓] [':: rewrite-::])
   (render-metafunction APP)))