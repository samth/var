#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt") 
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

(define-metafunction λc-raw
  annotator : (any ...) -> PROG
  [(annotator (any)) (annotator ((require) any))]
  [(annotator (any ...))
   PROG
   (where (any_m ... RREQ_1 any_e) (ann/define-contract (any ...)))   
   (where (RMOD_1 ...) ((expand-mod any_m) ...))
   (where MODENV (mod-env (RMOD_1 ...)))
   (where REQ (ann-req RREQ_1 MODENV))
   (where (MOD ...) ((ann-mod RMOD_1 MODENV) ...))
   (where EXP (ann-exp any_e † MODENV ()))
   (where PROG (MOD ... REQ EXP))])

(define-metafunction λc-raw
  ann/define-contract : (any ...) -> (any ...)
  [(ann/define-contract ((define-contract X RCON) any ...))
   (ann/define-contract (replace X RCON (any ...)))]
  [(ann/define-contract (any ...)) (any ...)])

(define (check-mod M)
  (unless (redex-match λc-raw RMOD M)
    (error 'module "not a module: ~a" M))
  #f)

(define (check-expr E)
  (unless (redex-match λc-raw REXP E)
    (error 'expr "not an expression: ~a" E))
  #f)

(define (check-req R)
  (unless (redex-match λc-raw RREQ R)
    (error 'require "not a require: ~a" R))
  #f)

(define-metafunction λc-raw
  mod-env : (RMOD ...) -> MODENV
  [(mod-env ((module X_nam LANG any ... (provide/contract [X_exp any_c] ...)) ...))
   MODENV
   (where MODENV ([X_nam (X_exp ...)] ...))])

;; Annotate RE with inside module LAB, using MODENV module environment and (f ...) local environment.
(define-metafunction λc-raw
  ann-exp : REXP LAB MODENV (X ...) -> EXP
  [(ann-exp VAL LAB MODENV (X_m ...)) VAL]
  [(ann-exp X_1 X_2 MODENV (X_4 ... X_1 X_3 ...))  ; local reference
   (X_1 ^ X_2 X_2)]      
  [(ann-exp X_1 LAB (any_4 ... (X_3 (X_5 ... X_1 X_6 ...)) any_7 ...) any) ; non-local reference
   (X_1 ^ LAB X_3)]
  
  [(ann-exp X LAB MODENV any) X]
  [(ann-exp (cond [else REXP]) LAB MODENV any)
   (ann-exp REXP LAB MODENV any)]
  [(ann-exp (cond [REXP REXP_1] [REXP_2 REXP_3] ... [else REXP_4]) LAB MODENV any)
   (ann-exp (if REXP REXP_1
                (cond [REXP_2 REXP_3] ... [else REXP_4]))
            LAB MODENV any)]
  [(ann-exp (or) LAB MODENV any)
   (ann-exp #t LAB MODENV any)]
  [(ann-exp (or REXP) LAB MODENV any)
   (ann-exp REXP LAB MODENV any)]
  [(ann-exp (or REXP_0 REXP_1 ...) LAB MODENV any)
   (if (ann-exp REXP_0 LAB MODENV any)
       #t
       (ann-exp (or REXP_1 ...) LAB MODENV any))]
  [(ann-exp (and) LAB MODENV any)
   (ann-exp #f LAB MODENV any)]
  [(ann-exp (and REXP) LAB MODENV any)
   (ann-exp REXP LAB MODENV any)]
  [(ann-exp (and REXP_0 REXP_1 ...) LAB MODENV any)
   (if (ann-exp REXP_0 LAB MODENV any)
       (ann-exp (and REXP_1 ...) LAB MODENV any)
       #f)]
  [(ann-exp (if REXP_0 REXP_1 REXP_2) LAB MODENV (X_m ...))
   (if (ann-exp REXP_0 LAB MODENV (X_m ...))
       (ann-exp REXP_1 LAB MODENV (X_m ...))
       (ann-exp REXP_2 LAB MODENV (X_m ...)))]
  [(ann-exp (OP REXP ...) LAB MODENV (X_m ...))
   (@ OP (ann-exp REXP LAB MODENV (X_m ...)) ... LAB)]
  [(ann-exp (let ((X REXP_0) ...) REXP_1) LAB MODENV (X_m ...))
   (let ((X (ann-exp REXP_0 LAB MODENV (X_m ...))) ...)
     (ann-exp REXP_1 LAB (mod-env-minus MODENV (X ...)) (set-minus (X_m ...) (X ...))))]
  [(ann-exp (begin REXP_0 REXP_1) LAB MODENV (X_m ...))
   (begin (ann-exp REXP_0 LAB MODENV (X_m ...))
          (ann-exp REXP_1 LAB MODENV (X_m ...)))]
  [(ann-exp (begin REXP_0 REXP_1 REXP_2 ...) LAB MODENV (X_m ...))
   (begin (ann-exp REXP_0 LAB MODENV (X_m ...))
          (ann-exp (begin REXP_1 REXP_2 ...) LAB MODENV (X_m ...)))]
  [(ann-exp (λ (X ...) REXP) LAB MODENV (X_m ...))
   (λ (X ...) (ann-exp REXP LAB (mod-env-minus MODENV (X ...)) (set-minus (X_m ...) (X ...))))]
  [(ann-exp (λ X_f (X ...) REXP) LAB MODENV (X_m ...))
   (λ X_f (X ...) (ann-exp REXP LAB (mod-env-minus MODENV (X ... X_f)) (set-minus (X_m ...) (X ... X_f))))]  
  [(ann-exp (REXP_0 REXP_1 ...) LAB MODENV (X_m ...))
   (@ (ann-exp REXP_0 LAB MODENV (X_m ...))
      (ann-exp REXP_1 LAB MODENV (X_m ...))
      ...
      LAB)])

(define-metafunction λc-raw
  mod-env-minus : MODENV (X ...) -> MODENV
  [(mod-env-minus ((X_1 (X_2 ...)) ...) (X_3 ...))
   ((X_1 (set-minus (X_2 ...) (X_3 ...))) ...)])

(test
 (test-equal (term (ann-exp f g ((g (f))) (f))) (term (f ^ g g)))
 (test-equal (term (ann-exp f † ((g (f))) ())) (term (f ^ † g)))
 (test-equal (term (ann-exp f † () ())) (term f))
 (test-equal (term (ann-exp (zero? x) † () ())) (term (@ zero? x †)))
 (test-equal (term (ann-exp (f x) † () ())) (term (@ f x †))))

(define-metafunction λc-raw 
  unfold-def : RDEF -> RDEF
  [(unfold-def (define (X_f X ...) REXP))
   (define X_f (λ X_f (X ...) REXP))]
  [(unfold-def RDEF) RDEF])

(define-metafunction λc-raw
  ann-req : RREQ MODENV -> REQ
  [(ann-req (require any ...) MODENV) (require (ann-one-req any MODENV) ...)])

(define-metafunction λc-raw
  ann-one-req : any MODENV -> any
  [(ann-one-req (only-in X X_1 ...) MODENV) (only-in X X_1 ...)]
  [(ann-one-req (only-in 'X X_1 ...) MODENV) (only-in X X_1 ...)] 
  [(ann-one-req 'X MODENV) (ann-one-req X MODENV)]
  [(ann-one-req X MODENV) 
   (only-in X X_1 ...)
   (where (any_1 ... (X [X_1 ...]) any_2 ...) MODENV)]
  [(ann-one-req X MODENV)  ;; Unbound module reference
   (only-in X)])


(define-metafunction λc-raw
  expand-mod : RMOD -> RMOD
  ;; define/contract as shorthand
  [(expand-mod (define/contract X RCON any))
   (module X racket (require) (define X any) (provide/contract [X RCON]))]
  ;; combine requires into one, add if missing
  [(expand-mod (module X LANG (require any_relem ...) ... RSTRUCT ... RDEF ... (provide/contract [X_3 RCON] ...)))
   (expand-mod (module X LANG (require any_relem ... ...) RSTRUCT ... RDEF ... (provide/contract [X_3 RCON] ...)))
   (side-condition (not (= 1 (length (term ((require any_relem ...) ...))))))]
  ;; fill in definitions if there are no definitions
  [(expand-mod (module X LANG
                 (require any_relem ...)
                 (provide/contract [X_3 RCON] ...)))
   (module X LANG
     (require any_relem ...)
     (define X_3 •)
     ...
     (provide/contract [X_3 RCON] ...))]
  [(expand-mod RMOD) RMOD])

(define-metafunction λc-raw
  ann-mod : RMOD MODENV -> MOD
  [(ann-mod (module X LANG 
              RREQ
              RSTRUCT ...
              RDEF ...
              (provide/contract [X_3 RCON] ...))
            MODENV)
   (module X LANG
     (require (only-in X_1 X_2 ...) ...)
     RSTRUCT ...
     (define X_4 (ann-rhs any X ((X_1 (X_2 ...)) ...) (X_4 ... X_s ...)))
     ...
     (provide/contract [X_3 (ann-con RCON X ((X_1 (X_2 ...)) ...) (X_4 ... X_s ...))] ...))
   (where (require (only-in X_1 X_2 ...) ...) (ann-req RREQ MODENV))   
   (where ((define X_4 any) ...) ((unfold-def RDEF) ...))
   (where (X_s ...) (rstruct-names RSTRUCT ...))])

(define-metafunction λc-raw
  rstruct-names : RSTRUCT ... -> (X ...)
  [(rstruct-names RSTRUCT ...)
   (X ... ...)
   (where ((X ...) ...) ((rstruct-name RSTRUCT) ...))])
(define-metafunction λc-raw
  rstruct-name : RSTRUCT -> (X ...)
  [(rstruct-name (struct X_cons (X_fld ...)))
   (X_cons ,(string->symbol (format "~a?" (term X_cons))) X_acc ...)
   (where (X_acc ...)
          ,(map (λ (f) (string->symbol (format "~a-~a" (term X_cons) f)))
                (term (X_fld ...))))])

(define-metafunction λc-raw
  ann-rhs : any X MODENV (X ...) -> • or EXP
  [(ann-rhs bullet X_1 MODENV (X ...)) •]
  [(ann-rhs REXP X_1 MODENV (X ...))
   (ann-exp REXP X_1 MODENV (X ...))])

(define-metafunction λc-raw
  ann-con : RCON LAB MODENV (X ...) -> CON ;or (pred f f)
  [(ann-con ATOMLIT LAB MODENV (X ...))
   (atom/c ATOMLIT LAB)]
  [(ann-con (one-of/c ATOMLIT) LAB MODENV (X ...))
   (ann-con ATOMLIT LAB MODENV (X ...))]
  [(ann-con (one-of/c ATOMLIT_1 ATOMLIT_2 ...) LAB MODENV (X ...))
   (ann-con (or/c ATOMLIT_1
                  (one-of/c ATOMLIT_2 ...))
            LAB MODENV (X ...))]
  [(ann-con (symbols 'variable ...) LAB MODENV (X ...))
   (ann-con (one-of/c 'variable ...) LAB MODENV (X ...))]
  [(ann-con (list/c) LAB MODENV (X ...))
   (ann-con empty LAB MODENV (X ...))]
  [(ann-con (list/c RCON_1 RCON_2 ...) LAB MODENV (X ...))
   (ann-con (cons/c RCON_1 (list/c RCON_2 ...)) LAB MODENV (X ...))]
  [(ann-con OP LAB MODENV (X ...))
   (pred OP LAB)]
  [(ann-con (listof RCON) LAB MODENV (X ...))
   ,(let ((x (gensym)))
      (term (ann-con (rec/c ,x (or/c empty? (cons/c RCON ,x))) LAB MODENV (X ...))))]
  [(ann-con (non-empty-listof RCON) LAB MODENV (X ...))
   (ann-con (cons/c RCON (listof RCON)) LAB MODENV (X ...))]
  [(ann-con any/c LAB MODENV (X ...))
   (pred (λ (x) #t) LAB)]
  [(ann-con (pred RL) LAB MODENV (X ...))
   (pred (ann-exp RL LAB MODENV (X ...)) LAB)]
  
  ;; We cheat by re-using the expression annotator for module references
  [(ann-con (pred X) LAB MODENV (X_1 ...))
   (pred MODREF LAB)
   (where MODREF (ann-exp X LAB MODENV (X_1 ...)))]  
  [(ann-con X LAB MODENV (X_1 ...))
   (ann-con (pred X) LAB MODENV (X_1 ...))
   (where ((any_f (X_s ...)) ...) MODENV)
   (where (any ... X any_1 ...) (X_s ... ... X_1 ...))]
  [(ann-con (pred OP) LAB MODENV (X ...))
   (pred OP LAB)]
  ;; ---
  [(ann-con (cons/c RCON_0 RCON_1) LAB MODENV (X ...))
   (cons/c (ann-con RCON_0 LAB MODENV (X ...))
           (ann-con RCON_1 LAB MODENV (X ...)))]  
  [(ann-con (struct/c X RCON_0 ...) LAB MODENV (X_1 ...))
   (struct/c X_cons X_def (ann-con RCON_0 LAB MODENV (X_1 ...)) ...)
   (where (X_cons ^ LAB X_def)
          (ann-exp X LAB MODENV (X_1 ...)))]
  [(ann-con (not/c RCON_0) LAB MODENV (X ...))
   (not/c (ann-con RCON_0 LAB MODENV (X ...)))]
  [(ann-con (and/c RCON_0 RCON_1) LAB MODENV (X ...))
   (and/c (ann-con RCON_0 LAB MODENV (X ...))
          (ann-con RCON_1 LAB MODENV (X ...)))]
  [(ann-con (or/c RCON_0 RCON_1) LAB MODENV (X ...))
   (or/c (ann-con RCON_0 LAB MODENV (X ...))
         (ann-con RCON_1 LAB MODENV (X ...)))]
  [(ann-con (rec/c X_c RCON) LAB MODENV (X ...))
   (rec/c X_c (ann-con RCON LAB MODENV (X ...)))]
  
  [(ann-con (RARR RCON_0 ... RCON_1) LAB MODENV (X ...))
   ((ann-con RCON_0 LAB MODENV (X ...)) ... -> (ann-con RCON_1 LAB MODENV (X ...)))]
  [(ann-con (RARR RCON_0 ... (λ (X_c ...) RCON_1)) LAB MODENV (X ...))
   ((ann-con RCON_0 LAB MODENV (X ...)) ... -> (λ (X_c ...) (ann-con RCON_1 LAB MODENV (X ...))))]
  [(ann-con (pred X) LAB MODENV (X_1 ...)) 
   (pred (λ (x) "this is the fall-through case") ★)]
  [(ann-con RCON LAB MODENV (X ...)) RCON])


(define-metafunction λcρ
  set-minus : (any ...) (any ...) -> (any ...)
  [(set-minus any_0 any_1)
   ,(set->list (set-subtract  (apply set (term any_0))
                              (apply set (term any_1))))])

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
 (redex-check λc-raw RP (redex-match λc-raw P (term (ann RP))))
 
 ;; Broken by adding realish modules.
 #|
 (test-equal (term (ann ,fit-example-raw)) fit-example)
 (test-equal (term (ann ,list-id-example-raw)) list-id-example)
 |#
 (test-equal (term (annotator ((module f racket (require) (define g 1) (provide/contract [g any/c]))
                               (require)
                               (λ (f) f))))
             (term ((module f racket (require) (define g 1) (provide/contract [g (pred (λ (x) #t) f)])) 
                    (require)
                    (λ (f) f)))))

(test 
 (test-equal
  (term (annotator
         [(module m racket            
            (define (f z) z)
            (provide/contract [f (any/c . -> . any/c)]))
          (require 'm)
          (f 3)]))
  (term [(module m racket
           (require)           
           (define f (λ f (z) z))
           (provide/contract (f ((pred (λ (x) #t) m) -> (pred (λ (x) #t) m)))))
         (require (only-in m f))
         (@ (f ^ † m) 3 |†|)]))
 
 (test-equal
  (term (annotator
         [(module p racket
            (struct posn (x y))
            (provide/contract [posn any/c]))
          (module m racket
            (require 'p)
            (define (f) (posn 1 2))
            (provide/contract [f (-> (struct/c posn any/c any/c))]))
          (require 'm)
          4]))
  (term [(module p racket
           (require)
           (struct posn (x y))
           (provide/contract [posn (pred (λ (x) #t) p)]))
         (module m racket
           (require (only-in p posn))
           (define f (λ f () (@ (posn ^ m p) 1 2 m)))
           (provide/contract [f (-> (struct/c posn p (pred (λ (x) #t) m) (pred (λ (x) #t) m)))]))
         (require (only-in m f))
         4])))
        
 



(define-metafunction λc-raw
  replace : any any any -> any
  [(replace any any_1 any) any_1]
  [(replace any_1 any_2 (any_3 ...))
   ((replace any_1 any_2 any_3) ...)]
  [(replace any any_1 any_2) any_2])

(test
 (test-equal (term (replace x 3 x)) (term 3))
 (test-equal (term (replace (y) 3 ((y) (y) (y)))) (term (3 3 3)))
 (test-equal (term (replace x 3 (q r s))) (term (q r s))))