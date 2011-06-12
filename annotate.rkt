#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "examples.rkt" "name.rkt" "util.rkt") 
(provide (except-out (all-defined-out) test))
(test-suite test annotate)

(define-metafunction λc~
  ann/define-contract : (any ...) -> P
  [(ann/define-contract ((define-contract x C) any ...))
   (ann/define-contract (subst x C (any ...)))]
  [(ann/define-contract (any ...))
   (ann (any ...))])
           
;; Annotate a "raw" program with labels, @, etc.
(define-metafunction λc~
  ann : RP -> P
  [(ann ((module f RC any) ... RE))
   ((ann-mod (module f RC any) (f ...)) ...        
    (ann-exp RE † (f ...)))])

;; Annotate RE with context f, using (f ...) module variables.
(define-metafunction λc~
  ann-exp : RE ℓ (f ...) -> E
  [(ann-exp f f any) (f ^ f)]
  [(ann-exp f ℓ (f_0 ... f f_1 ...)) (f ^ ℓ)]
  [(ann-exp x ℓ any) x]
  [(ann-exp (if RE_0 RE_1 RE_2) ℓ (f ...))
   (if (ann-exp RE_0 ℓ (f ...))
       (ann-exp RE_1 ℓ (f ...))
       (ann-exp RE_2 ℓ (f ...)))]
  [(ann-exp (o RE ...) ℓ (f ...))
   (@ o (ann-exp RE ℓ (f ...)) ... ℓ)]
  [(ann-exp (let x RE_0 RE_1) ℓ (f ...))
   (let x (ann-exp RE_0 ℓ (f ...))
     (ann-exp RE_1 ℓ (f ...)))]
  [(ann-exp (begin RE_0 RE_1) ℓ (f ...))
   (begin (ann-exp RE_0 ℓ (f ...))
          (ann-exp RE_1 ℓ (f ...)))]  
  [(ann-exp (λ x ... RE) ℓ (f ...))
   (λ x ... (ann-exp RE ℓ (f ...)))]
  [(ann-exp FV ℓ (f ...)) FV]
  [(ann-exp (RE_0 RE_1 ...) ℓ (f ...))
   (@ (ann-exp RE_0 ℓ (f ...))
      (ann-exp RE_1 ℓ (f ...))
      ...
      ℓ)])

(test
 (test-equal (term (ann-exp f f ())) (term (f ^ f)))
 (test-equal (term (ann-exp f † (f))) (term (f ^ †)))
 (test-equal (term (ann-exp f † ())) (term f))
 (test-equal (term (ann-exp (zero? x) † ())) (term (@ zero? x †)))
 (test-equal (term (ann-exp (f x) † ())) (term (@ f x †))))

(define-metafunction λc~
  ann-mod : RM (f ...) -> M
  [(ann-mod (module f RC RE) (f_0 ...)) 
   (module f (ann-con RC f (f_0 ...)) (ann-exp RE f (f_0 ...)))]
  [(ann-mod (module f RC ☁) (f_0 ...))
   (module f (ann-con RC f (f_0 ...)) ☁)])

(define-metafunction λc~
  ann-con : RC ℓ (f ...) -> C  
  [(ann-con (pred RL) ℓ (f ...))
   (pred (ann-exp RL ℓ (f ...)) ℓ)]
  [(ann-con (pred f) ℓ (f_0 ... f f_1 ...))
   (pred (f ^ ℓ) ℓ)] 
  [(ann-con (pred o1) ℓ (f ...))
   (pred o1 ℓ)]
  ;; ---
  ;; For random testing only
  ;; Well-formed programs do not have unbound module references.
  [(ann-con (pred f) ℓ (f_0 ...))
   (pred (f ^ f) ℓ)]
  ;; ---
  [(ann-con (cons/c RC_0 RC_1) ℓ (f ...))
   (cons/c (ann-con RC_0 ℓ (f ...))
           (ann-con RC_1 ℓ (f ...)))]
  [(ann-con (and/c RC_0 RC_1) ℓ (f ...))
   (and/c (ann-con RC_0 ℓ (f ...))
          (ann-con RC_1 ℓ (f ...)))]
  [(ann-con (RC_0 -> RC_1) ℓ (f ...))
   ((ann-con RC_0 ℓ (f ...)) -> (ann-con RC_1 ℓ (f ...)))]
  [(ann-con RC ℓ (f ...)) RC])

(test
 (test-equal (term (ann-con (pred f) g (f)))
             (term (pred (f ^ g) g)))
 
 ;; Totality test
 (redex-check λc~ RP (redex-match λc~ P (term (ann RP))))
 
 (test-equal (term (ann ,fit-example-raw)) fit-example)
 (test-equal (term (ann ,list-id-example-raw)) list-id-example))

#;
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
