#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "examples.rkt" "subst.rkt" "util.rkt") 
(provide (except-out (all-defined-out) test))
(test-suite test annotate)

#|
(module m racket
  (require (only-in m f ...) ...)
  (struct f (x ...))
  ...
  (define f PV)
  ...
  (provide/contract [f C] ...))
...
(require (only-in m f ...) ...)
E
|#

(define-metafunction λc~
  ann/define-contract : (any ...) -> P
  [(ann/define-contract ((define-contract x RCON) any ...))
   (ann/define-contract (replace x RCON (any ...)))]
  [(ann/define-contract (any ...))
   (ann (any ...))])

(define (check-mod M)
  (unless (redex-match λc~ RMOD M)
    (error 'module "not a module: ~a" M))
  #f)

(define (check-expr E)
  (unless (redex-match λc~ REXP E)
    (error 'expr "not an expression: ~a" E))
  #f)

(define (check-req R)
  (unless (redex-match λc~ RREQ R)
    (error 'require "not a require: ~a" R))
  #f)
           
;; Annotate a "raw" program with labels, @, etc.
(define-metafunction λc~
  ann : any -> P
  [(ann (any_m ... any_r any_e)) ,(error "should never happen")
   (side-condition (or (ormap check-mod (term (any_m ...)))
                       (check-req (term any_r))
                       (check-expr (term any_e))))]
  [(ann (RMOD ...
         RREQ
         REXP))
   ((ann-mod RMOD MODENV) ...
    (require (only-in f_4 f_5 ...) ...)
    (ann-exp REXP † ((f_4 (f_5 ...)) ...) ()))   
   (where ((module f_nam LANG any ... (provide/contract [f_exp any_c] ...)) ...) (RMOD ...))
   (where MODENV ([f_nam (f_exp ...)] ...))
   (where (require (only-in f_4 f_5 ...) ...) (ann-req (RREQ) MODENV))])

;; Annotate RE with inside module ℓ, using MODENV module environment and (f ...) local environment.
(define-metafunction λc~
  ann-exp : REXP ℓ MODENV (f ...) -> E  
  [(ann-exp f_1 f_2 MODENV (f_4 ... f_1 f_3 ...))  ; local reference
   (f_1 ^ f_2 f_2)]      
  [(ann-exp f_1 ℓ (any_4 ... (f_3 (f_5 ... f_1 f_6 ...)) any_7 ...) any) ; non-local reference
   (f_1 ^ ℓ f_3)]
  
  [(ann-exp x ℓ MODENV any) x]
  [(ann-exp (if REXP_0 REXP_1 REXP_2) ℓ MODENV (f ...))
   (if (ann-exp REXP_0 ℓ MODENV (f ...))
       (ann-exp REXP_1 ℓ MODENV (f ...))
       (ann-exp REXP_2 ℓ MODENV (f ...)))]
  [(ann-exp (op REXP ...) ℓ MODENV (f ...))
   (@ op (ann-exp REXP ℓ MODENV (f ...)) ... ℓ)]
  [(ann-exp (let ((x REXP_0) ...) REXP_1) ℓ MODENV (f ...))
   (let ((x (ann-exp REXP_0 ℓ MODENV (f ...))) ...)
     (ann-exp REXP_1 ℓ (mod-env-minus MODENV (x ...)) (set-minus (f ...) (x ...))))]
  [(ann-exp (begin REXP_0 REXP_1) ℓ MODENV (f ...))
   (begin (ann-exp REXP_0 ℓ MODENV (f ...))
          (ann-exp REXP_1 ℓ MODENV (f ...)))]  
  [(ann-exp (λ (x ...) REXP) ℓ MODENV (f ...))
   (λ (x ...) (ann-exp REXP ℓ (mod-env-minus MODENV (x ...)) (set-minus (f ...) (x ...))))]
  [(ann-exp (λ x_f (x ...) REXP) ℓ MODENV (f ...))
   (λ x_f (x ...) (ann-exp REXP ℓ (mod-env-minus MODENV (x ... x_f)) (set-minus (f ...) (x ... x_f))))]
  [(ann-exp FV ℓ MODENV (f ...)) FV]
  [(ann-exp (REXP_0 REXP_1 ...) ℓ MODENV (f ...))
   (@ (ann-exp REXP_0 ℓ MODENV (f ...))
      (ann-exp REXP_1 ℓ MODENV (f ...))
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
  [(unfold-def (define (f x ...) REXP))
   (define f (λ f (x ...) REXP))]
  [(unfold-def RDEF) RDEF])

(define-metafunction λc~
  ann-req : (RREQ ...) MODENV -> R
  [(ann-req ((require (only-in f ...) ...) ...) MODENV) (require (only-in f ...) ... ...)]
  [(ann-req ((require any ...) ...) MODENV) (ann-req ((require (ann-one-req any MODENV) ...) ...) MODENV)])

(define-metafunction λc~
  ann-one-req : any MODENV -> any
  [(ann-one-req (only-in f f_1 ...) MODENV) (only-in f f_1 ...)]
  [(ann-one-req f MODENV) 
   (only-in f f_1 ...)
   (where (any_1 ... (f [f_1 ...]) any_2 ...) MODENV)])

(define-metafunction λc~
  ann-mod : RMOD MODENV -> M
  [(ann-mod (define/contract f RCON any) MODENV)
   (ann-mod (module f racket (require) (define f any) (provide/contract [f RCON])) MODENV)]
  [(ann-mod (module f LANG 
              RREQ ...
              RSTRUCT ...
              RDEF ...
              (provide/contract [f_3 RCON] ...))
            MODENV)
   (ann-mod
    (module f LANG
      R
      RSTRUCT ...
      RDEF ...
      (provide/contract [f_3 RCON] ...))
    MODENV)
   (where R (ann-req (RREQ ...) MODENV))
   (side-condition (not (redex-match λc~ (R) (term (RREQ ...)))))]
  [(ann-mod (module f LANG
              (provide/contract [f_3 RCON] ...))
            MODENV)
   (module f LANG
     (require)
     (define f_3 ☁)
     ...
     (provide/contract [f_3 (ann-con RCON f () (f_3 ...))] ...))]
  [(ann-mod (module f LANG
              (require (only-in f_1 f_2 ...) ...)
              RSTRUCT ...
              (provide/contract [f_3 RCON] ...))
            MODENV)
   (module f LANG
     (require (only-in f_1 f_2 ...) ...)
     RSTRUCT ...
     (define f_3 ☁)
     ...
     (provide/contract [f_3 (ann-con RCON f ((f_1 (f_2 ...)) ...) (f_3 ...))] ...))]
  [(ann-mod (module f LANG (require (only-in f_1 f_2 ...) ...) 
              RSTRUCT ...
              RDEF ...
              (provide/contract [f_3 RCON] ...))
            MODENV)
   (module f LANG
     (require (only-in f_1 f_2 ...) ...)
     RSTRUCT ...
     (define f_4 (ann-rhs any f ((f_1 (f_2 ...)) ...) (f_4 ...)))
     ...
     (provide/contract [f_3 (ann-con RCON f ((f_1 (f_2 ...)) ...) (f_4 ...))] ...))
   (where ((define f_4 any) ...) ((unfold-def RDEF) ...))])

(define-metafunction λc~
  ann-rhs : any f MODENV (f ...) -> ☁ or E
  [(ann-rhs bullet f_1 MODENV (f ...)) ☁]
  [(ann-rhs REXP f_1 MODENV (f ...))
   (ann-exp REXP f_1 MODENV (f ...))])

(define-metafunction λc~
  ann-con : RCON ℓ MODENV (f ...) -> C ;or (pred f f)
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
   (ann-con (pred f) ℓ MODENV (f_1 ...))
   (where ((any_f (f_s ...)) ...) MODENV)
   (where (any ... f any_1 ...) (f_s ... ... f_1 ...))]
  [(ann-con (pred o1) ℓ MODENV (f ...))
   (pred o1 ℓ)]
  ;; ---
  [(ann-con (cons/c RCON_0 RCON_1) ℓ MODENV (f ...))
   (cons/c (ann-con RCON_0 ℓ MODENV (f ...))
           (ann-con RCON_1 ℓ MODENV (f ...)))]
  [(ann-con (and/c RCON_0 RCON_1) ℓ MODENV (f ...))
   (and/c (ann-con RCON_0 ℓ MODENV (f ...))
          (ann-con RCON_1 ℓ MODENV (f ...)))]
  [(ann-con (or/c RCON_0 RCON_1) ℓ MODENV (f ...))
   (or/c (ann-con RCON_0 ℓ MODENV (f ...))
         (ann-con RCON_1 ℓ MODENV (f ...)))]
  [(ann-con (rec/c x RCON) ℓ MODENV (f ...))
   (rec/c x (ann-con RCON ℓ MODENV (f ...)))]
  
  [(ann-con (RCON_0 ... RARR RCON_1) ℓ MODENV (f ...))
   ((ann-con RCON_0 ℓ MODENV (f ...)) ... -> (ann-con RCON_1 ℓ MODENV (f ...)))]
  [(ann-con (RCON_0 ... RARR (λ (x ...) RCON_1)) ℓ MODENV (f ...))
   ((ann-con RCON_0 ℓ MODENV (f ...)) ... -> (λ (x ...) (ann-con RCON_1 ℓ MODENV (f ...))))]
  [(ann-con (pred f) ℓ MODENV (f_1 ...)) 
   (pred (λ (x) "this is the fall-through case") ★)]
  [(ann-con RCON ℓ MODENV (f ...)) RCON])

(test
 (test-equal (term (ann-con (even? -> even?) dbl ([e/o (even?)]) (dbl)))
             (term ((pred (even? ^ dbl e/o) dbl) -> (pred (even? ^ dbl e/o) dbl))))
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

