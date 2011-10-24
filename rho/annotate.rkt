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

#|

Pass 0: insert omitted require 
Pass 1: expand `define-contract'
Pass 2: expand shorthands
 - (define (f x) E)
 - (require foo)
 - missing opaque defs
 - omitted requires
Pass 3: Annotate expressions/predicates
 - add @
 - expand modules references

|#

(define-metafunction λc~
  annotator : (any ...) -> P
  [(annotator (any)) (annotator ((require) any))]
  [(annotator (any ...))
   P
   (where (any_m ... RREQ_1 any_e) (ann/define-contract (any ...)))   
   (where (RMOD_1 ...) ((expand-mod any_m) ...))
   (where MODENV (mod-env (RMOD_1 ...)))
   (where R (ann-req RREQ_1 MODENV))
   (where (M ...) ((ann-mod RMOD_1 MODENV) ...))
   (where E (ann-exp any_e † MODENV ()))
   (where P (M ... R E))])

(define-metafunction λc~
  ann/define-contract : (any ...) -> (any ...)
  [(ann/define-contract ((define-contract x RCON) any ...))
   (ann/define-contract (replace x RCON (any ...)))]
  [(ann/define-contract (any ...)) (any ...)])

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

(define-metafunction λc~
  mod-env : (RMOD ...) -> MODENV
  [(mod-env ((module f_nam LANG any ... (provide/contract [f_exp any_c] ...)) ...))
   MODENV
   (where MODENV ([f_nam (f_exp ...)] ...))])

;; Annotate RE with inside module ℓ, using MODENV module environment and (f ...) local environment.
(define-metafunction λc~
  ann-exp : REXP ℓ MODENV (f ...) -> E  
  [(ann-exp f_1 f_2 MODENV (f_4 ... f_1 f_3 ...))  ; local reference
   (f_1 ^ f_2 f_2)]      
  [(ann-exp f_1 ℓ (any_4 ... (f_3 (f_5 ... f_1 f_6 ...)) any_7 ...) any) ; non-local reference
   (f_1 ^ ℓ f_3)]
  
  [(ann-exp x ℓ MODENV any) x]
  [(ann-exp (cond [else REXP]) ℓ MODENV any)
   (ann-exp REXP ℓ MODENV any)]
  [(ann-exp (cond [REXP REXP_1] [REXP_2 REXP_3] ... [else REXP_4]) ℓ MODENV any)
   (ann-exp (if REXP REXP_1
                (cond [REXP_2 REXP_3] ... [else REXP_4]))
            ℓ MODENV any)]
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
  ann-req : RREQ MODENV -> R  
  [(ann-req (require any ...) MODENV) (require (ann-one-req any MODENV) ...)])

(define-metafunction λc~
  ann-one-req : any MODENV -> any
  [(ann-one-req (only-in f f_1 ...) MODENV) (only-in f f_1 ...)]
  [(ann-one-req (only-in 'f f_1 ...) MODENV) (only-in f f_1 ...)] 
  [(ann-one-req 'f MODENV) (ann-one-req f MODENV)]
  [(ann-one-req f MODENV) 
   (only-in f f_1 ...)
   (where (any_1 ... (f [f_1 ...]) any_2 ...) MODENV)]
  [(ann-one-req f MODENV)  ;; Unbound module reference
   (only-in f)])


(define-metafunction λc~
  expand-mod : RMOD -> RMOD
  ;; define/contract as shorthand
  [(expand-mod (define/contract f RCON any))
   (module f racket (require) (define f any) (provide/contract [f RCON]))]
  ;; combine requires into one, add if missing
  [(expand-mod (module f LANG (require any_relem ...) ... RSTRUCT ... RDEF ... (provide/contract [f_3 RCON] ...)))
   (expand-mod (module f LANG (require any_relem ... ...) RSTRUCT ... RDEF ... (provide/contract [f_3 RCON] ...)))
   (side-condition (not (= 1 (length (term ((require any_relem ...) ...))))))]
  ;; fill in definitions if there are no definitions
  [(expand-mod (module f LANG
                 (require any_relem ...)
                 (provide/contract [f_3 RCON] ...)))
   (module f LANG
     (require any_relem ...)
     (define f_3 •)
     ...
     (provide/contract [f_3 RCON] ...))]
  [(expand-mod RMOD) RMOD])

(define-metafunction λc~
  ann-mod : RMOD MODENV -> M  
  [(ann-mod (module f LANG 
              RREQ
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
   (where (require (only-in f_1 f_2 ...) ...) (ann-req RREQ MODENV))
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
  
  [(ann-con (RARR RCON_0 ... RCON_1) ℓ MODENV (f ...))
   ((ann-con RCON_0 ℓ MODENV (f ...)) ... -> (ann-con RCON_1 ℓ MODENV (f ...)))]
  [(ann-con (RARR RCON_0 ... (λ (x ...) RCON_1)) ℓ MODENV (f ...))
   ((ann-con RCON_0 ℓ MODENV (f ...)) ... -> (λ (x ...) (ann-con RCON_1 ℓ MODENV (f ...))))]
  [(ann-con (pred f) ℓ MODENV (f_1 ...)) 
   (pred (λ (x) "this is the fall-through case") ★)]
  [(ann-con RCON ℓ MODENV (f ...)) RCON])

(test 
 (test-equal (term (ann-con (-> even? even?) dbl ([e/o (even?)]) (dbl)))
             (term ((pred (even? ^ dbl e/o) dbl) -> (pred (even? ^ dbl e/o) dbl))))
 (test-equal (term (ann-con f g ((h (f))) ()))
             (term (pred (f ^ g h) g)))
 (test-equal (term (ann-con j g ((h (f))) (j)))
             (term (pred (j ^ g g) g)))
 
 (test-equal (term (ann-con (pred f) g ((h (f))) ()))
             (term (pred (f ^ g h) g)))
 
 ;; Totality test
 ;; BROKEN BY ALL KINDS OF VIOLATED ASSUMPTIONS LIKE SAME NAMES DEFINED IN DIFFERENT MODULES
 #;
 (redex-check λc~ RP (redex-match λc~ P (term (ann RP))))
 
 ;; Broken by adding realish modules.
 #|
 (test-equal (term (ann ,fit-example-raw)) fit-example)
 (test-equal (term (ann ,list-id-example-raw)) list-id-example)
 |#
 (test-equal (term (annotator ((module f racket (require) (define g 1) (provide/contract [g anything]))
                               (require)
                               (λ (f) f))))
             (term ((module f racket (require) (define g 1) (provide/contract [g (pred (λ (x) #t) f)])) 
                    (require)
                    (λ (f) f)))))



