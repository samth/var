#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "test.rkt") 
(provide (all-defined-out))

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

(test-equal (term (ann-exp f f ())) (term (f ^ f)))
(test-equal (term (ann-exp f † (f))) (term (f ^ †)))
(test-equal (term (ann-exp f † ())) (term f))
(test-equal (term (ann-exp (zero? x) † ())) (term (@ zero? x †)))
(test-equal (term (ann-exp (f x) † ())) (term (@ f x †)))

(define-metafunction λc~
  ann-mod : RM (f ...) -> M
  [(ann-mod (module f RC RE) (f_0 ...)) 
   (module f (ann-con RC f (f_0 ...)) (ann-exp RE f (f_0 ...)))]
  [(ann-mod (module f RC ☁) (f_0 ...))
   (module f (ann-con RC f (f_0 ...)) ☁)])

(define-metafunction λc~
  ann-con : RC ℓ (f ...) -> C  
  [(ann-con (pred RL) ℓ (f ...))
   (pred (ann-exp RL ℓ (f ...)))]  
  [(ann-con (pred f) ℓ (f_0 ... f f_1 ...))
   (pred (f ^ ℓ))]  
  ;; ---
  ;; For random testing only
  ;; Well-formed programs do not have unbound module references.
  [(ann-con (pred f) ℓ (f_0 ...))
   (pred (f ^ f))]
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

(test-equal (term (ann-con (pred f) g (f)))
            (term (pred (f ^ g))))
  
;; Totality test
(redex-check λc~ RP (redex-match λc~ P (term (ann RP))))
       
(test-equal (term (ann ,fit-example-raw)) fit-example)
(test-equal (term (ann ,list-id-example-raw)) list-id-example)