#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "examples.rkt" "subst.rkt" "util.rkt") 
(provide (except-out (all-defined-out) test))
(test-suite test annotate)

#|
(module m racket
  (require (only-in m f ...) ...)
  (define f PV)
  ...
  (provide/contract [f C] ...))
...
(require (only-in m f ...) ...)
E
|#

(define-metafunction λc~
  ann/define-contract : (any ...) -> P
  [(ann/define-contract ((define-contract x RC) any ...))
   (ann/define-contract (replace x RC (any ...)))]
  [(ann/define-contract (any ...))
   (ann (any ...))])
           
;; Annotate a "raw" program with labels, @, etc.
(define-metafunction λc~
  ann : RP -> P
  [(ann (RM ...
         (require (only-in f_4 f_5 ...) ...)
         RE))
   ((ann-mod RM) ...
    (require (only-in f_4 f_5 ...) ...)
    (ann-exp RE † ((f_4 (f_5 ...)) ...) ()))])

;; Annotate RE with inside module ℓ, using MODENV module environment and (f ...) local environment.
(define-metafunction λc~
  ann-exp : RE ℓ MODENV (f ...) -> E  
  [(ann-exp f_1 f_2 MODENV (f_4 ... f_1 f_3 ...))  ; local reference
   (f_1 ^ f_2 f_2)]      
  [(ann-exp f_1 ℓ (any_4 ... (f_3 (f_5 ... f_1 f_6 ...)) any_7 ...) any) ; non-local reference
   (f_1 ^ ℓ f_3)]
  
  [(ann-exp x ℓ MODENV any) x]
  [(ann-exp (if RE_0 RE_1 RE_2) ℓ MODENV (f ...))
   (if (ann-exp RE_0 ℓ MODENV (f ...))
       (ann-exp RE_1 ℓ MODENV (f ...))
       (ann-exp RE_2 ℓ MODENV (f ...)))]
  [(ann-exp (o RE ...) ℓ MODENV (f ...))
   (@ o (ann-exp RE ℓ MODENV (f ...)) ... ℓ)]
  [(ann-exp (let x RE_0 RE_1) ℓ MODENV (f ...))
   (let x (ann-exp RE_0 ℓ MODENV (f ...))
     (ann-exp RE_1 ℓ (mod-env-minus MODENV (x)) (set-minus (f ...) (x))))]
  [(ann-exp (begin RE_0 RE_1) ℓ MODENV (f ...))
   (begin (ann-exp RE_0 ℓ MODENV (f ...))
          (ann-exp RE_1 ℓ MODENV (f ...)))]  
  [(ann-exp (λ (x ...) RE) ℓ MODENV (f ...))
   (λ (x ...) (ann-exp RE ℓ (mod-env-minus MODENV (x ...)) (set-minus (f ...) (x ...))))]
  [(ann-exp (λ x_f (x ...) RE) ℓ MODENV (f ...))
   (λ x_f (x ...) (ann-exp RE ℓ (mod-env-minus MODENV (x ... x_f)) (set-minus (f ...) (x ... x_f))))]
  [(ann-exp FV ℓ MODENV (f ...)) FV]
  [(ann-exp (RE_0 RE_1 ...) ℓ MODENV (f ...))
   (@ (ann-exp RE_0 ℓ MODENV (f ...))
      (ann-exp RE_1 ℓ MODENV (f ...))
      ...
      ℓ)])

(define-metafunction λc~
  mod-env-minus : MODENV (f ...) -> MODENV
  [(mod-env-minus ((f_1 (f_2 ...)) ...) (f_3 ...))
   ((f_1 (set-minus (f_2 ...) (f_3 ...))) ...)])

(test
 (test-equal (term (ann-exp f g ((g (f))) (f))) (term (f ^ g g)))
 (test-equal (term (ann-exp f † ((g (f))) ())) (term (f ^ † g)))
 (test-equal (term (ann-exp f † () ())) (term f))
 (test-equal (term (ann-exp (zero? x) † () ())) (term (@ zero? x †)))
 (test-equal (term (ann-exp (f x) † () ())) (term (@ f x †))))

(define-metafunction λc~ 
  unfold-def : RDEF -> RDEF
  [(unfold-def (define (f x ...) RE))
   (define f (λ f (x ...) RE))]
  [(unfold-def RDEF) RDEF])

(define-metafunction λc~
  ann-mod : RM -> M
  [(ann-mod (module f LANG (require (only-in f_1 f_2 ...) ...) 
              RDEF ...
              (provide/contract [f_3 RC] ...)))
   (module f LANG
     (require (only-in f_1 f_2 ...) ...)
     (define f_4 (ann-rhs any f ((f_1 (f_2 ...)) ...) (f_4 ...)))
     ...
     (provide/contract [f_3 (ann-con RC f ((f_1 (f_2 ...)) ...) (f_4 ...))] ...))
   (where ((define f_4 any) ...) ((unfold-def RDEF) ...))]
  [(ann-mod (module f LANG
              (provide/contract [f_3 RC] ...)))
   (module f LANG
     (require)
     (define f_3 ☁)
     ...
     (provide/contract [f_3 (ann-con RC f () (f_3 ...))] ...))]
  [(ann-mod (module f LANG
              (require (only-in f_1 f_2 ...) ...)
              (provide/contract [f_3 RC] ...)))
   (module f LANG
     (require (only-in f_1 f_2 ...) ...)
     (define f_3 ☁)
     ...
     (provide/contract [f_3 (ann-con RC f ((f_1 (f_2 ...)) ...) (f_3 ...))] ...))])

(define-metafunction λc~
  ann-rhs : any f MODENV (f ...) -> ☁ or E
  [(ann-rhs bullet f_1 MODENV (f ...)) ☁]
  [(ann-rhs RE f_1 MODENV (f ...))
   (ann-exp RE f_1 MODENV (f ...))])

(define-metafunction λc~
  ann-con : RC ℓ MODENV (f ...) -> C ;or (pred f f)
  [(ann-con o? ℓ MODENV (f ...))
   (pred o? ℓ)]  
  [(ann-con anything ℓ MODENV (f ...))
   (pred (λ (x) #t) ℓ)]
  [(ann-con any? ℓ MODENV (f ...))
   (pred (λ (x) #t) ℓ)]
  [(ann-con (pred RL) ℓ MODENV (f ...))
   (pred (ann-exp RL ℓ MODENV (f ...)) ℓ)]
  
  ;; We cheat by re-using the expression annotator for module references
  [(ann-con (pred f) ℓ MODENV (f_1 ...))
   (pred MODREF ℓ)
   (where MODREF (ann-exp f ℓ MODENV (f_1 ...)))]
  [(ann-con f ℓ MODENV (f_1 ...))
   (ann-con (pred f) ℓ MODENV (f_1 ...))]
  [(ann-con (pred o1) ℓ MODENV (f ...))
   (pred o1 ℓ)]
  ;; ---
  [(ann-con (cons/c RC_0 RC_1) ℓ MODENV (f ...))
   (cons/c (ann-con RC_0 ℓ MODENV (f ...))
           (ann-con RC_1 ℓ MODENV (f ...)))]
  [(ann-con (and/c RC_0 RC_1) ℓ MODENV (f ...))
   (and/c (ann-con RC_0 ℓ MODENV (f ...))
          (ann-con RC_1 ℓ MODENV (f ...)))]
  [(ann-con (or/c RC_0 RC_1) ℓ MODENV (f ...))
   (or/c (ann-con RC_0 ℓ MODENV (f ...))
         (ann-con RC_1 ℓ MODENV (f ...)))]
  [(ann-con (rec/c x RC) ℓ MODENV (f ...))
   (rec/c x (ann-con RC ℓ MODENV (f ...)))]
  
  [(ann-con (RC_0 ... RARR RC_1) ℓ MODENV (f ...))
   ((ann-con RC_0 ℓ MODENV (f ...)) ... -> (ann-con RC_1 ℓ MODENV (f ...)))]
  [(ann-con (RC_0 ... RARR (λ (x ...) RC_1)) ℓ MODENV (f ...))
   ((ann-con RC_0 ℓ MODENV (f ...)) ... -> (λ (x ...) (ann-con RC_1 ℓ MODENV (f ...))))]
  [(ann-con RC ℓ MODENV (f ...)) (pred (λ (x) "this is the fall-through case") ★)])

(test
 (test-equal (term (ann-con f g ((h (f))) ()))
             (term (pred (f ^ g h) g)))
 (test-equal (term (ann-con j g ((h (f))) (j)))
             (term (pred (j ^ g g) g)))
 
 (test-equal (term (ann-con (pred f) g ((h (f))) ()))
             (term (pred (f ^ g h) g)))
 
 ;; Totality test
 (redex-check λc~ RP (redex-match λc~ P (term (ann RP))))
 
 ;; Broken by adding realish modules.
 #|
 (test-equal (term (ann ,fit-example-raw)) fit-example)
 (test-equal (term (ann ,list-id-example-raw)) list-id-example)
 |#
 (test-equal (term (ann ((module f racket (require) (define g 1) (provide/contract [g anything]))
                         (require)
                         (λ (f) f))))
             (term ((module f racket (require) (define g 1) (provide/contract [g (pred (λ (x) #t) f)])) 
                    (require)
                    (λ (f) f)))))

;; below stuff is bitrotted

#|
(define-metafunction λc~
  unann : P -> RP
  [(unann (M ... E))
   ((unann-mod M) ... (unann-exp E))])

(define-metafunction λc~
  unann-exp : E -> any
  [(unann-exp (@ o any ... ℓ))
   (o (unann-exp any) ...)]
  [(unann-exp (@ any ... ℓ))
   ((unann-exp any) ...)]
  [(unann-exp (f ^ ℓ)) f]
  [(unann-exp (-- C_0 C ...))
   (-- (unann-con C_0))]
  [(unann-exp (-- PV C ...))
   (unann-exp PV)]
  [(unann-exp (C <= ℓ_0 ℓ_1 V-or-x ℓ_2 E))
   ((unann-con C) ⇐ (unann-exp E))]
  [(unann-exp (blame ℓ_0 ℓ_1 V_0 C V))
   (blame ℓ_0 ℓ_1 (unann-exp V_0) (unann-con C) (unann-exp V))]
  ;; if, begin, let
  [(unann-exp (any E ...))
   (any (unann-exp E) ...)]
  [(unann-exp E) E])

(define-metafunction λc~
  unann-con : C -> any
  [(unann-con (pred E ℓ))
   (pred (unann-exp E))]
  [(unann-con (C_0 -> C_1))
   ((unann-con C_0) -> (unann-con C_1))]
  ;; or/c, and/c, cons/c
  [(unann-con (any C_0 C_1))
   (any (unann-con C_0) (unann-con C_1))]
  [(unann-con C) C])
|#
