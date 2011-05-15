#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "test.rkt")                

(define-metafunction λc~
  ann : RP -> P
  [(ann ((module f RC any) ... RE))
   ((ann-mod (module f RC any) (f ...)) ...        
    (ann-exp RE † (f ...)))])

;; Annotate RE with context f, using (f ...) module variables.
(define-metafunction λc~
  ann-exp : RE f (f ...) -> E
  [(ann-exp f f any) (f ^ f)]
  [(ann-exp f f_2 (f_0 ... f f_1 ...)) (f ^ f_2)]
  [(ann-exp x f any) x]
  [(ann-exp (if RE_0 RE_1 RE_2) f (f_0 ...))
   (if (ann-exp RE_0 f (f_0 ...))
       (ann-exp RE_1 f (f_0 ...))
       (ann-exp RE_2 f (f_0 ...)))]
  [(ann-exp (o RE ...) f (f_0 ...))
   (@ o (ann-exp RE f (f_0 ...)) ... f)]
  [(ann-exp (let x RE_0 RE_1) f (f_0 ...))
   (let x (ann-exp RE_0 f (f_0 ...))
     (ann-exp RE_1 f (f_0 ...)))]
  [(ann-exp (begin RE_0 RE_1) f (f_0 ...))
   (begin (ann-exp RE_0 f (f_0 ...))
          (ann-exp RE_1 f (f_0 ...)))]  
  [(ann-exp (λ x ... RE) f (f_0 ...))
   (λ x ... (ann-exp RE f (f_0 ...)))]
  [(ann-exp FV f (f_0 ...)) FV]
  [(ann-exp (RE_0 RE_1 ...) f (f_0 ...))
   (@ (ann-exp RE_0 f (f_0 ...))
      (ann-exp RE_1 f (f_0 ...))
      ...
      f)])

(define-metafunction λc~
  ann-mod : RM (f ...) -> M
  [(ann-mod (module f RC RE) (f_0 ...)) 
   (module f (ann-con RC f (f_0 ...)) (ann-exp RE f (f_0 ...)))]
  [(ann-mod (module f RC ☁) (f_0 ...))
   (module f (ann-con RC f (f_0 ...)) ☁)])

(define-metafunction λc~
  ann-con : RC f (f ...) -> C
  [(ann-con (pred RSV) f (f_0 ...))
   (pred (ann-exp RSV f (f_0 ...)))]
  [(ann-con (RC_0 -> RC_1) f (f_0 ...))
   ((ann-con RC_0 f (f_0 ...)) -> (ann-con RC_1 f (f_0 ...)))]
  [(ann-con RC f (f_0 ...)) RC])
  
  
(test-equal (term (ann ,fit-example-raw)) fit-example)
(test-equal (term (ann ,list-id-example-raw)) list-id-example)