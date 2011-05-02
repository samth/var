#lang racket
(require redex)

;;-------
;; Experimenting with Racket subset.
(define-language λc-racket
  (P (module top racket/load M ... (require 'f) ... E))
  (M (module f racket (provide/contract [f C]) (require 'f) ... (define f V)))
  (L (λ (x) E))
  (V n L)
  (E V x f (E E) (if E E E))
  (C exact-integer? any/c (-> C C) L)
  (x variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned)
  (n integer))

(define example-8-racket
  (term (module top racket/load
          (module f racket 
            (provide/contract [f (-> any/c (-> any/c any/c))])
            (define f (λ (x) x)))
          #;(module g racket
            (provide/contract [g (-> (λ (x) (= x 0)) exact-integer?)])
            (define g (λ (x) 0)))
          (module h racket
            (provide/contract [h any/c])
            (require 'f)
            (require 'g)
            (define h (λ (z) ((f g) 8))))
          (require 'h)
          (h 0))))

(test-predicate (redex-match λc-racket P) example-8-racket)
;;-------

;; TODO: Add operations.

;; Figure 5.
(define-language λc-user
  (P (M ... E))
  (M (module f C V))
  (L (λ x E))
  (W L)
  (V n #t #f W string) 
  (SV L f) ; Syntactic values for pred.  [Different than paper]
  (E V x (f ^ f) (E E f) (if E E E) (o1 E f) (o2 E E f))
  (C int any/c string/c (C -> C) (pred SV))
  (x variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned o †) ;; † is top-level
  (n integer)
  (o o1 o2)
  (o1 add1 sub1 zero?)
  (o2 + - * expt = < <= > >=)
  (𝓔 hole (𝓔 E f) (V 𝓔 f) (if 𝓔 E E) (o V ... 𝓔 E ... f)))
  
;; Figure 5, gray (cont).
(define-extended-language λc λc-user
  (W .... ((C --> C) <= f f V f W))
  (B (blame f f V C V))
  (E .... (C <= f f V f E) B)
  (C .... (C --> C) λ)
  (f .... Λ)
  (𝓔 .... (C <= f f V f 𝓔)))

;; Figure 5, gray (cont).
(define-extended-language λc~ λc
  (V .... (-- C))                       ;; (-- X) is overline X.
  (B .... (blame f? g? V1? C? V2?))
  (M .... (module f C ☁))
  (W .... (-- (C -> C)) (-- (pred L)))
  
  ;; CEK stuff
  (s (E ρ κ))
  (ρ ((x V) ...))
  (κ mt (ar f E ρ κ) (fn f V ρ κ) (if E E ρ κ) (ck f f V f C κ)))

;; Current reductions give:
;; (prime? (-- prime?))
;; -> ((--> int any/c) (-- prime?))
;;
;; b/c: 
;; prime? -> (--> int any/c)

;; Want:
;; (prime? (-- prime?))
;; -> #t

;; (prime? V)
;; -> ((-- (--> int any/c)) V)    if V != (-- prime?)

;; ((f ^ g) (-- (pred f))) --> #t
;; ((f ^ g) V)             --> ((-- C) V)      where V != (-- (pred f)), (module f C ☁) in P.

;; (let ((x = f)) (x V))



(define fit-example
  (term [(module prime? (int -> any/c) ☁)
         (module rsa ((pred prime?) -> (string/c -> string/c)) ☁)
         (module keygen (any/c -> (pred prime?)) ☁)
         (((rsa ^ †) ((keygen ^ †) #f †) †) "Plain" †)]))

(define fit-example-alt
  (term [(module prime? (int -> any/c) ☁)
         (module rsa (string/c -> ((pred prime?) -> string/c)) ☁)
         (module keygen (any/c -> (pred prime?)) ☁)
         (((rsa ^ †) "Plain" †) ((keygen ^ †) #f †) †)]))


;; Modified from Figure 8 in paper (8 -> #f).
(define example-8
  (term [(module f (any/c -> (any/c -> any/c)) (λ x x))
         (module g ((pred (λ x x)) -> int) (λ x 0))
         (module h any/c (λ z (((f ^ h) (g ^ h) h) #f h)))
         ((h ^ †) 0 †)]))

(test-predicate (redex-match λc-user P) example-8)
(test-predicate (redex-match λc P) example-8)
(test-predicate (redex-match λc~ P) example-8)

(test-predicate (redex-match λc~ P) fit-example)
(test-predicate (redex-match λc~ P) fit-example-alt)

(define-metafunction λc~
  [(δ (add1 n f)) ,(add1 (term n))]
  [(δ (sub1 n f)) ,(sub1 (term n))]
  [(δ (zero? n f)) ,(zero? (term n))]
  [(δ (o1 V f)) (blame f o1 V λ V)]
  [(δ (+ n_1 n_2 f)) ,(+ (term n_1) (term n_2))]
  [(δ (- n_1 n_2 f)) ,(- (term n_1) (term n_2))]
  [(δ (* n_1 n_2 f)) ,(* (term n_1) (term n_2))]
  [(δ (expt n_1 n_2 f)) ,(expt (term n_1) (term n_2))]
  [(δ (= n_1 n_2 f)) ,(= (term n_1) (term n_2))]
  [(δ (< n_1 n_2 f)) ,(< (term n_1) (term n_2))]
  [(δ (<= n_1 n_2 f)) ,(<= (term n_1) (term n_2))]
  [(δ (> n_1 n_2 f)) ,(> (term n_1) (term n_2))]  
  [(δ (>= n_1 n_2 f)) ,(>= (term n_1) (term n_2))]
  ;; FIXME: should refer to V_1 and V_2.
  [(δ (o2 V_1 V_2 f)) (blame f o2 V_1 λ V_1)])

(test-equal (term (δ (add1 0 f))) +1)
(test-equal (term (δ (sub1 0 f))) -1)
(test-equal (term (δ (zero? 0 f))) #t)
(test-equal (term (δ (zero? 1 f))) #f)
(test-equal (term (δ (add1 #t f))) (term (blame f add1 #t λ #t)))

;; Test for δ totalness.
(redex-check λc~ (o1 V)
             (or (redex-match λc~ V (term (δ (o1 V f))))
                 (equal? (term (blame f o1 V λ V))
                         (term (δ (o1 V f))))))
(redex-check λc~ (o2 V_1 V_2)
             (or (redex-match λc~ V (term (δ (o2 V_1 V_2 f))))
                 (redex-match λc~ B (term (δ (o2 V_1 V_2 f))))))



(define-metafunction λc~ subst : x any any -> any  
  ;; 1. x bound, so don't continue in λ body  
  [(subst x any_1 (λ x any_2)) 
   (λ x any_2)] 
  ;; 2. general purpose capture avoiding case  
  [(subst x_1 any_1 (λ x_2 any_2)) 
   (λ x_new
     (subst x_1 any_1 (subst-var x_2 x_new any_2))) 
   (where x_new 
          ,(variable-not-in (term (x_1 any_1 any_2)) 
                            (term x_2)))]  
  ;; 3. replace x_1 with e_1  
  [(subst x_1 any_1 x_1) any_1]  
  ;; 4. x_1 and x_2 are different, so don't replace  
  [(subst x_1 any_1 x_2) x_2]  
  ;; the last cases cover all other expressions  
  [(subst x_1 any_1 (any_2 ...)) 
   ((subst x_1 any_1 any_2) ...)] 
  [(subst x_1 any_1 any_2) 
   any_2])

(define-metafunction λc~ subst-var : x any any -> any 
  [(subst-var x_1 any_1 x_1) any_1] 
  [(subst-var x_1 any_1 (any_2 ...)) 
   ((subst-var x_1 any_1 any_2) ...)] 
  [(subst-var x_1 any_1 any_2) any_2])

(test-equal (term (subst x 0 x)) (term 0))
(test-equal (term (subst x 0 y)) (term y))
(test-equal (term (subst x 0 (λ x x))) (term (λ x x)))

(define v
  (reduction-relation
   λc~ #:domain E
   (--> ((λ x E) V f) (subst x V E) β)
   (--> (n V f) (blame f Λ n λ n) wrong)
   (--> (if V E_1 E_2) E_1 
        (side-condition (term V))
        if-t)
   (--> (if V E_1 E_2) E_2 
        (side-condition (not (term V)))
        if-f)))
   
(test--> v (term ((λ x 0) 1 †)) (term 0))
(test--> v (term (0 1 †)) (term (blame † Λ 0 λ 0)))
(test--> v (term (if 0 1 2)) (term 1))
(test--> v (term (if #t 1 2)) (term 1))
(test--> v (term (if #f 1 2)) (term 2))

(define (Δ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f ^ f)
        V
        (where (M_1 ... (module f C V) M_2 ...) ,Ms)
        Δ-self)
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 V f_1 V)
        (where (M_1 ... (module f_1 C V) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2))))
        Δ-other)))

(test--> (Δ (term [(module f any/c 0)]))
         (term (f ^ f))
         (term 0))
(test--> (Δ (term [(module f any/c 0)]))
         (term (f ^ g))
         (term (any/c <= f g 0 f 0)))

(define (Δ~ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f ^ f)
        V
        (where (M_1 ... (module f C V) M_2 ...) ,Ms))
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 V f_1 V)
        (where (M_1 ... (module f_1 C V) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2)))))
   (--> (f_1 ^ f_2)
        (-- C)
        (where (M_1 ... (module f_1 C ☁) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2)))))
   
   ;; New reductions
   (--> ((f_1 ^ f_2) (-- (pred f_1)) f_3)
        #t
        smart-check)))
   
   

(test--> (Δ~ (term [(module f any/c ☁)]))
         (term (f ^ g))
         (term (-- any/c)))

(define c
  (reduction-relation
   λc~ #:domain E
   (--> (((C_1 --> C_2) <= f_1 f_2 V_1 f_3 W) V_2 f_4)
        (C_2 <= f_1 f_2 V_1 f_3 (W (C_1 <= f_2 f_1 V_1 f_3 V_2) f_4))
        split)   
   (--> (int <= f_1 f_2 V f_3 n) n chk-int-pass)
   (--> (int <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 int V_2)
        (side-condition (not (integer? (term V_2))))
        chk-int-fail)
   (--> (string/c <= f_1 f_2 V f_3 string) string chk-string-pass)   ;; new
   (--> (string/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 string/c V_2)
        (side-condition (not (string? (term V_2))))
        chk-string-fail)   
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 W)
        ((C_1 --> C_2) <= f_1 f_2 V f_3 W)
        chk-fun-pass)
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 n)
        (blame f_1 f_3 V (C_1 -> C_2) n)
        chk-fun-fail)
   (--> ((pred L) <= f_1 f_2 V_1 f_3 V_2)
        (if (L V_2 Λ) V_2 (blame f_1 f_3 V_1 (pred L) V_2))
        chk-pred)
   
   ;; sugar
   (--> (any/c <= f_1 f_2 V_1 f_3 V_2) V_2 any-pass)))

;; when we get blame, discard the context
(define error-propagate
  (reduction-relation 
   λc~ #:domain E
   (--> (in-hole 𝓔 B) B
        (side-condition (not (equal? (term hole) (term 𝓔)))))))


(test--> c 
         (term (((any/c --> any/c) <= f g 7 f (λ x 5)) 8 †))
         (term (any/c <= f g 7 f ((λ x 5) (any/c <= g f 7 f 8) †))))
(test--> c (term (int <= f g 0 f 5)) (term 5))
(test--> c 
         (term (int <= f g 0 f (λ x x))) 
         (term (blame f f 0 int (λ x x))))
(test--> c 
         (term (int <= f g 0 f #t)) 
         (term (blame f f 0 int #t)))
(test--> c
         (term ((any/c  -> any/c) <= f g 0 f (λ x x)))
         (term ((any/c --> any/c) <= f g 0 f (λ x x))))
(test--> c 
         (term ((any/c  -> any/c) <= f g 0 f 5))
         (term (blame f f 0 (any/c -> any/c) 5)))
(test--> c
         (term ((pred (λ x 0)) <= f g 0 f 5))
         (term (if ((λ x 0) 5 Λ)
                   5
                   (blame f f 0 (pred (λ x 0)) 5))))

(define c~
  (reduction-relation
   λc~ #:domain E
   (--> ((-- (pred L)) V f)
        (-- any/c))
   (--> ((-- (pred L)) V f)
        (blame f? g? V1? C? V2?))
   ;; C_1 dropped on floor entirely.  Fix and work around soundness problem.
   ;; Should be more like the split rule.
   ;; Check C_1 <= V; (-- C_2)
   (--> ((-- (C_1 -> C_2)) V f)
        (-- C_2))
   (--> ((-- (C_1 -> C_2)) V f)
        (blame f? g? V1? C? V2?))
   (--> ((-- int) V)
        (blame f Λ (-- int) λ (-- int)))
   (--> (if (-- C) E_1 E_2)
        E_2)
   (--> (if (-- C) E_1 E_2)
        E_1)
   (--> (int <= f_1 f_2 V f_3 (-- int))
        (-- int))
   (--> (int <= f_1 f_2 V f_3 (-- (pred L)))
        (-- int))
   (--> (int <= f_1 f_2 V f_3 (-- (pred L)))
        (blame f_1 f_3 V int (-- (pred L))))
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- (pred L)))
        (-- (C_1 -> C_2)))
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- (pred L)))
        (blame f_1 f_3 V (C_1 -> C_2) (-- (pred L))))
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- int))
        (blame f_1 f_3 V (C_1 -> C_2) (-- int)))
   
   ;; sugar
   (--> ((-- any/c) V f)
        (-- any/c))
   (--> ((-- any/c) V f)
        (blame f? g? V1? C? V2?)) 
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- any/c))
        (blame f_1 f_3 V (C_1 -> C_2) (-- any/c)))   
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- any/c))
        (-- (C_1 -> C_2)))
   (--> (int <= f_1 f_2 V f_3 (-- any/c))
        (-- int))
   (--> (int <= f_1 f_2 V f_3 (-- any/c))
        (blame f_1 f_3 V int (-- any/c)))))
   
   
(define example-8-opaque
  (term [(module f (any/c -> (any/c -> any/c)) ☁)
         (module g ((pred (λ x x)) -> int) ☁)
         (module h any/c (λ z (((f ^ h) (g ^ h) h) 8 h)))
         ((h ^ †) 0 †)]))


(test-predicate (redex-match λc~ P) example-8-opaque)

(define (all-but-last ls)
  (cond [(empty? (rest ls)) empty]
        [else (cons (first ls)
                    (all-but-last (rest ls)))]))
  
(define (-->_vcΔ Ms)
  (union-reduction-relations error-propagate (context-closure (union-reduction-relations v c (Δ Ms)) λc~ 𝓔)))

(define (-->_vcc~Δ Ms)
  (union-reduction-relations error-propagate (context-closure (union-reduction-relations v c c~ (Δ~ Ms)) λc~ 𝓔)))


(define (eval_vcΔ P)
  (apply-reduction-relation* (-->_vcΔ (all-but-last P))
                             (last P)))

(define (eval_vcc~Δ P)
  (apply-reduction-relation* (-->_vcc~Δ (all-but-last P))
                             (last P)))


(define-syntax-rule (trace-it R P)
  (traces (R (all-but-last P))
          (last P)))

(trace-it -->_vcc~Δ fit-example)


(test-predicate (redex-match λc 
                  [(in-hole 𝓔 (blame h g (λ x 0) (pred (λ x x)) #f))])
                (eval_vcΔ example-8))
#;
(traces (-->_vcΔ (all-but-last example-8))
        (last example-8))
#;
(traces (-->_vcc~Δ (all-but-last example-8-opaque))
        (last example-8-opaque))


;; CEK machine

(define-metafunction λc~ inj_CEK : E -> S
  [(inj_CEK E) (E () mt)])



