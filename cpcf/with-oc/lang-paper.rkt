#lang racket
(require redex)
(require (only-in "lang-paper-simple.rkt"
                  λrec δ [close close′] ! :: [A→EA A→EA′] rewrite-! rewrite-::))
(provide sλrec ⇓ APP Δ proves? ev A→EA not-•? var-not-in vars-not-in close :: !
         render-⇓ render-APP render-Δ)

(define-extended-language sλrec λrec
  [v .... •]
  [φ p? (¬ p?)]
  
  [σ ([l ↦ V] ...)]
  
  ; closure
  [V .... (★ V ...) l]
  [W ((λ x e) ρ) ((rec (f x) e) ρ) b (Cons V V) (★ V ...)]
  [l variable-not-otherwise-mentioned]
  
  [EA b function ERR • (• V ...) (Cons EA EA)])

(define-judgment-form sλrec
  #:mode     (⇓ I I I O O)
  #:contract (⇓ σ ρ e A σ)
  [----- "err"
         (⇓ σ ρ err ERR σ)]
  [(where l (var-not-in σ L))
   ----- "•"
   (⇓ σ ρ • l [:: σ (l ↦ (★))])]
  [(side-condition (not-•? v))
   ----- "val"
   (⇓ σ ρ v [close v ρ] σ)]
  [----- "var"
         (⇓ σ ρ x [! ρ x] σ)]
  [(⇓ σ ρ e_f V_f σ_1)
   (⇓ σ_1 ρ e_x V_x σ_2)
   (APP σ_2 V_f [V_x] A σ_3)
   ----- "app1"
   (⇓ σ ρ (e_f e_x) A σ_3)]
  [(⇓ σ ρ e_f V_f σ_1)
   (⇓ σ_1 ρ e_x V_x σ_2)
   (⇓ σ_2 ρ e_y V_y σ_3)
   (APP σ_3 V_f [V_x V_y] A σ_4)
   ----- "app2"
   (⇓ σ ρ (e_f e_x e_y) A σ_4)]
  [(⇓ σ ρ e_f ERR σ_1)
   ----- "app-err1"
   (⇓ σ ρ (e_f e_x ...) ERR σ_1)]
  [(⇓ σ ρ e_f V_f σ_1)
   (⇓ σ_1 ρ e_x ERR σ_2)
   ----- "app-err2"
   (⇓ σ ρ (e_f e_x e_y ...) ERR σ_2)]
  [(⇓ σ ρ e_f V_f σ_1)
   (⇓ σ_1 ρ e_x V_x σ_2)
   (⇓ σ_2 ρ e_y ERR σ_3)
   ----- "app-err3"
   (⇓ σ ρ (e_f e_x e_y) ERR σ_3)]
  
  [(⇓ σ ρ e V_t σ_1)
   (Δ σ_1 false? [V_t] #f σ_2)
   (⇓ σ_2 ρ e_1 A σ_3)
   ----- "if-true"
   (⇓ σ ρ (if e e_1 e_2) A σ_3)]
  [(⇓ σ ρ e V_t σ_1)
   (Δ σ_1 false? [V_t] #t σ_2)
   (⇓ σ_2 ρ e_2 A σ_3)
   ----- "if-false"
   (⇓ σ ρ (if e e_1 e_2) A σ_3)]
  [(⇓ σ ρ e ERR σ_1)
   ----- "if-err"
   (⇓ σ ρ (if e e_1 e_2) ERR σ_1)])

(define-judgment-form sλrec
  #:mode     (APP I I I       O O)
  #:contract (APP σ V [V ...] A σ)
  [(⇓ σ [:: ρ [f ↦ ((rec (f x) e) ρ)] [x ↦ V]] e A σ_1)
   ----- "APP-rec"
   (APP σ ((rec (f x) e) ρ) [V] A σ_1)]
  [(⇓ σ [:: ρ (x ↦ V)] e A σ_1)
   ----- "APP-λ"
   (APP σ ((λ x e) ρ) [V] A σ_1)]
  [(Δ σ o [V ...] A σ_1)
   ----- "APP-Δ"
   (APP σ o [V ...] A σ_1)]
  
  [(APP σ [! σ l] [V ...] A σ_1)
   ----- "APP-l"
   (APP σ l [V ...] A σ_1)]
  
  [(Δ σ proc? [V_f] #f σ_1)
   ----- "APP-err"
   (APP σ V_f [V ...] ERR σ_1)]
  
  [(Δ σ proc? (★ V ...) #t σ_1)
   ----- "APP-havoc1"
   (APP σ (★ V ...) [V_x ...] (★) σ_1)]
  [(Δ σ proc? (★ V ...) #t σ_1)
   ----- "APP-havoc2"
   (APP σ (★ V ...) [V_x ...] ERR σ_1)])

(define-judgment-form sλrec
  #:mode     (Δ I I I       O O)
  #:contract (Δ σ o [V ...] A σ)
  
  ; primitive ops
  [(Δ σ p? [[! σ l]] #t σ_1)
   ----- "pred-l-ok"
   (Δ σ p? [l] #t [σ: σ_1 (l ↦ p?)])]
  [(Δ σ p? [[! σ l]] #f σ_1)
   ----- "pred-l-fail"
   (Δ σ p? [l] #f [σ: σ_1 (l ↦ (¬ p?))])]
  [(where Proved (proves? W p?))
   ----- "pred-ok"
   (Δ σ p? [W] #t σ)]
  [(where Refuted (proves? W p?))
   ----- "pred-fail"
   (Δ σ p? [W] #f σ)]
  [(where Neither (proves? W p?))
   ----- "pred-assumed-ok"
   (Δ σ p? [W] #t σ)]
  [(where Neither (proves? W p?))
   ----- "pred-assumed-fail"
   (Δ σ p? [W] #f σ)]
  
  ; sub1
  [(Δ σ add/sub1 [n] [δ add/sub1 n] σ)]
  [(Δ σ add/sub1 [V] (★ num?) σ_1)
   (side-condition (not-n? V))
   (Δ σ num? [V] #t σ_1)]
  [(Δ σ add/sub1 [V] ERR σ_1)
   (Δ σ num? [V] #f σ_1)]
  
  [(Δ σ +|-|* [m n] [δ +|-|* m n] σ)]
  [(Δ σ +|-|* [V_1 V_2] (★ num?) σ_2)
   (side-condition (OR (not-n? V_1) (not-n? V_2)))
   (Δ σ num? [V_1] #t σ_1)
   (Δ σ_1 num? [V_1] #t σ_2)]
  [(Δ σ +|-|* [V_1 V_2] ERR σ_1)
   (Δ σ num? [V_1] #f σ_1)]
  [(Δ σ +|-|* [V_1 V_2] ERR σ_2)
   (Δ σ num? [V_1] #t σ_1)
   (Δ σ_1 num? [V_2] #f σ_2)]
  
  [(Δ σ / [m n] (δ / m n) σ)]
  [(Δ σ / [V_1 V_2] ERR σ_1)
   (Δ σ num? [V_1] #f σ_1)]
  [(Δ σ / [V_1 V_2] ERR σ_2)
   (Δ σ num? [V_1] #t σ_1)
   (Δ σ num? [V_2] #f σ_2)]
  [(Δ σ / [V_1 V_2] ERR σ_2)
   (Δ σ num? [V_1] #t σ_1)
   (Δ σ zero? [V_2] #t σ_2)]
  [(Δ σ / [V_1 V_2] ERR σ_3)
   (Δ σ num? [V_1] #t σ_1)
   (Δ σ num? [V_2] #t σ_2)
   (Δ σ zero? [V_2] #f σ_3)]
  
  ; str-len
  [(Δ σ str-len [s] (δ str-len s) σ)]
  [(Δ σ str-len [V] ERR σ_1)
   (Δ σ str? [V] #f σ_1)]
  [(Δ σ str-len [V] (★ num?) σ_1)
   (side-condition (not-s? V))
   (Δ σ str? [V] #t σ_1)]
  
  [(Δ σ cons? [V] #f σ_1)
   ----- "acc-fail"
   (Δ σ acc [V] ERR σ_1)]
  [----- "car"
         (Δ σ car [(Cons V_1 V_2)] V_1 σ)]
  [----- "cdr"
         (Δ σ cdr [(Cons V_1 V_2)] V_2 σ)]
  [(Δ σ cons? [l] #t σ_1)
   (where (Cons V_1 V_2) (! σ_1 l))
   ----- "car-l"
   (Δ σ car [l] V_1 σ_1)]
  [(Δ σ cons? [l] #t σ_1)
   (where (Cons V_1 V_2) (! σ_1 l))
   ----- "cdr-l"
   (Δ σ cdr [l] V_2 σ_1)]
  [(Δ σ cons [V_1 V_2] (Cons V_1 V_2) σ)])

(define-metafunction sλrec
  proves? : W p? -> Verified?
  [(proves? 0 zero?) Proved]
  [(proves? n num?) Proved]
  [(proves? s str?) Proved]
  [(proves? #f false?) Proved]
  [(proves? #t true?) Proved]
  [(proves? (Cons V_1 V_2) cons?) Proved]
  [(proves? PROC proc?) Proved]
  [(proves? b p?) Refuted]
  [(proves? PROC p?) Refuted]
  [(proves? (★ V_1 ... p? V_i ...) p?_1)
   Proved
   (where Proved (implies? p? p?_1))]
  [(proves? (★ V_1 ... p? V_i ...) p?_1)
   Refuted
   (where Refuted (implies? p? p?_1))]
  [(proves? (★ V_1 ... ((λ x (false? (p? x))) ρ) V_i ...) p?_1)
   Refuted
   (where Proved (implies? p?_1 p?))]
  [(proves? W p?) Neither])

(define-metafunction sλrec
  implies? : p? p? -> Verified?
  [(implies? zero? num?) Proved]
  [(implies? p? p?) Proved]
  [(implies? p? p?_1)
   ,(if (ormap (λ (g) (and (member (term p?) g) (member (term p?_1) g)))
               '({num? str? true? false? cons? proc?}
                 {zero? str? true? false? cons? proc?}))
        (term Refuted)
        (term Neither))])

(define-metafunction sλrec
  σ: : σ [l ↦ φ] -> σ
  [(σ: (any_1 ... [l ↦ (★ V ...)] any_i ...) [l ↦ cons?])
   (any_1 ... [l ↦ (Cons l_1 l_2)] [l_1 ↦ (★)] [l_2 ↦ (★)] any_i ...)
   (where (l_1 l_2) (vars-not-in [any_1 ... l any_i ...] (l l)))]
  [(σ: (any_1 ... [l ↦ V] any_i ...) [l ↦ false?])
   (any_1 ... [l ↦ #f] any_i ...)]
  [(σ: (any_1 ... [l ↦ V] any_i ...) [l ↦ true?])
   (any_1 ... [l ↦ #t] any_i ...)]
  [(σ: (any_1 ... [l ↦ V] any_i ...) [l ↦ zero?])
   (any_1 ... [l ↦ 0] any_i ...)]
  [(σ: (any_1 ... [l ↦ (★ V ... p? V_1 ...)] any_i ...) [l ↦ p?])
   (any_1 ... [l ↦ (★ p? V ...)] any_i ...)]
  [(σ: (any_1 ... [l ↦ (★ V ...)] any_i ...) [l ↦ p?])
   (any_1 ... [l ↦ (★ p? V ...)] any_i ...)]
  [(σ: (any_1 ... [l ↦ (★ V ...)] any_i ...) [l ↦ (¬ p?)])
   (any_1 ... [l ↦ (★ [(λ X (false? (p? X))) ()] V ...)] any_i ...)]
  [(σ: σ [l ↦ φ]) σ])

(define-metafunction/extension close′ sλrec
  close : v ρ -> V)

(define-metafunction sλrec
  var-not-in : any x -> x
  [(var-not-in any x) ,(variable-not-in (term any) (term x))])
(define-metafunction sλrec
  vars-not-in : any [x ...] -> [x ...]
  [(vars-not-in any [x ...]) ,(variables-not-in (term any) (term [x ...]))])

(define-metafunction sλrec
  not-n? : any -> #t or #f
  [(not-n? n) #f] [(not-n? any) #t])
(define-metafunction sλrec
  not-•? : any -> #t or #f
  [(not-•? •) #f] [(not-•? any) #t])
(define-metafunction sλrec
  not-s? : any -> #t or #f
  [(not-s? s) #f] [(not-s? any) #t])
(define-metafunction sλrec
  OR : any ... -> #t or #f
  [(OR) #f]
  [(OR #f any ...) (OR any ...)]
  [(OR any_1 any ...) #t])

(define-metafunction sλrec
  A→EA : σ A -> EA
  [(A→EA σ l) (A→EA σ [! σ l])]
  [(A→EA σ (Cons V_1 V_2)) (Cons (A→EA σ V_1) (A→EA σ V_2))]
  [(A→EA σ (★)) •]
  [(A→EA σ (★ V ...)) (• V ...)]
  [(A→EA σ A) (A→EA′ A)])

(define-metafunction sλrec
  ev : e -> {EA ...}
  [(ev e)
   (remove-dups {(A→EA σ A) ...})
   (where ((A σ) ...) ,(judgment-holds (⇓ () () e A σ) (A σ)))])

(define-metafunction sλrec
  remove-dups : {any ...} -> {any ...}
  [(remove-dups {any_1 ... any any_2 ... any any_3 ...})
   (remove-dups {any_1 ... any any_2 ... any_3 ...})]
  [(remove-dups any) any])

(define (render-⇓
         [cs '("err" "•" "val" "var" "app1" "app2" "app-err1" "app-err2" "app-err3"
                     "it-true" "if-false" "if-err")])
  (with-compound-rewriters
   (['⇓ rewrite-⇓] ['! rewrite-!] [':: rewrite-::] ['Δ rewrite-Δ] ['APP rewrite-APP])
   (parameterize ([judgment-form-cases cs])
     (render-judgment-form ⇓))))

(define rewrite-⇓
  (match-lambda
    [`(,_ ,_ ,σ ,ρ ,e ,A ,σ′ ,_) `(,σ "," ,ρ " ⊢ " ,e " ⇓ " ,A "; " ,σ′)]))

(define (render-Δ [cs #f])
  (with-compound-rewriters
   (['Δ rewrite-Δ] ['! rewrite-!] [':: rewrite-::])
   (if cs
       (parameterize ([judgment-form-cases cs])
         (render-judgment-form Δ))
       (render-judgment-form Δ))))
(define rewrite-Δ
  (match-lambda
    [`(,_ ,_ ,σ ,o ,xs ,A ,σ′ ,_)
     `("Δ[" ,σ ", " ,o ", " ,xs "] ∋ <" ,A ", " ,σ′ ">")]))

(define rewrite-APP
  (match-lambda
    [`(,_ ,_ ,σ ,f ,xs ,A ,σ′ ,_)
     `("APP[" ,σ ", " ,f ", " ,xs "] ∋ <" ,A ", " ,σ′ ">")]))
(define (render-APP)
  (with-compound-rewriters
   (['⇓ rewrite-⇓] ['! rewrite-!] [':: rewrite-::] ['Δ rewrite-Δ] ['APP rewrite-APP])
   (render-judgment-form APP)))