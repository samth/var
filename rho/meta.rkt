#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
;(provide (all-from-out "meta-misc.rkt"))
(test-suite test meta)

(define-metafunction λcρ
  δ : OP V ... LAB -> (A A ...)
  ;; Concrete δ
  [(δ OP V ... LAB) 
   ((plain-δ OP V ... LAB))])

(define-metafunction λcρ
  plain-δ : OP V ... LAB -> A
  [(plain-δ cons V_0 V_1 LAB)
   (-- (cons V_0 V_1))]
  [(plain-δ procedure? PROC LAB)
   (-- (clos #t ()))]
  [(plain-δ procedure? V LAB)
   (-- (clos #f ()))]
  [(plain-δ string? (clos string ρ) LAB) 
   (-- (clos #t ()))]
  [(plain-δ string? V LAB) 
   (-- (clos #t ()))]
  [(plain-δ boolean? (-- (clos bool ρ) C ...) LAB) 
   (-- (clos #f ()))]
  [(plain-δ boolean? V LAB) 
   (-- (clos #f ()))]
  [(plain-δ zero? (-- (clos 0 ρ) C ...) LAB) 
   (-- (clos #t ()))]
  [(plain-δ zero? (-- (clos natural ρ) C ...) LAB) 
   (-- (clos #f ()))]  
  [(plain-δ empty? (-- (clos empty ρ) C ...)) 
   (-- (clos #t ()))]
  [(plain-δ empty? V LAB)
   (-- (clos #f ()))]
  [(plain-δ cons? (-- (cons V_0 V_1) C ...) LAB)
   (-- (clos #t ()))]    
  [(plain-δ cons? V LAB)
   (-- (clos #f ()))]  
  [(plain-δ exact-nonnegative-integer? (-- (clos natural ρ) C ...) LAB)
   (-- (clos #t ()))]
  [(plain-δ exact-nonnegative-integer? V LAB) 
   (-- (clos #f ()))]  
  [(plain-δ false? (-- (clos #f ρ) C ...) LAB) 
   (-- (clos #t ()))]
  [(plain-δ false? V LAB) 
   (-- (clos #f ()))]
  [(plain-δ add1 (-- (clos natural ρ) C ...) LAB)
   (-- (clos ,(add1 (term nat)) ()))]
  [(plain-δ sub1 (-- (clos 0 ρ) C ...) LAB)
   (-- (clos 0 ()))]
  [(plain-δ sub1 (-- (clos natural ρ) C ...) LAB)
   (-- (clos ,(sub1 (term natural)) ()))]
  [(plain-δ car (-- (cons V_0 V_1) C ...) LAB) V_0]
  [(plain-δ cdr (-- (cons V_0 V_1) C ...) LAB) V_1]
  [(plain-δ procedure-arity-includes? PROC (-- (clos natural ρ) C ...) LAB)
   ;; FIXME: tune up for ABSTRACT values   
   (-- (clos ,(= (term natural) (term (arity PROC))) ()))]
  ;; Interpreted differently than Racket `-'.
  [(plain-δ -
            (-- (clos natural_1 ρ_1) C_1 ...)
            (-- (clos natural_2 ρ_2) C_2 ...)
            LAB)
   (-- (clos ,(max 0 (- (term natural_1) (term natural_2))) ()))]
  [(plain-δ natural-natural->natural
            (-- (clos natural_1 ρ_1) C_1 ...)
            (-- (clos natural_2 ρ_2) C_2 ...)
            LAB)
   (meta-apply natural-natural->natural natural_1 natural_2)]   
  [(plain-δ natural-natural->boolean
            (-- (clos natural_1 ρ_1) C_1 ...)
            (-- (clos natural_2 ρ_2) C_2 ...)
            LAB)
   (meta-apply natural-natural->bool natural_1 natural_2)]
  [(plain-δ string-string->bool
            (-- (clos string_1 ρ_1) C_1 ...)
            (-- (clos string_2 ρ_2) C_2 ...)
            LAB)
   (meta-apply string-string->bool string_1 string_2)]
  [(plain-δ OP V V_1 ... LAB)       ;; catches domain errors
   (blame LAB Λ V OP V)])

(define-metafunction λcρ
  meta-apply : OP any ... -> D
  [(meta-apply OP any ...)
   (-- (clos ,(apply (lift (term OP)) (term (any ...))) ()))])

(define (lift f)
  (define-syntax reflect
    (syntax-rules ()
      [(reflect id ...)
       (case f [(id) id] ...)]))
  (reflect + - * expt = < <= > >=               
           string=? string<? string>? string<=? string>=?
           string-ci=? string-ci<? string-ci>? string-ci<=? string-ci>=?))

(define-metafunction λcρ 
  ∈ : any (any ...) -> #t or #f
  [(∈ any (any_0 ... (-- any) any_1 ...)) #t]
  [(∈ any (any_0 ... (-- (clos any ρ) C ...) any_1 ...)) #t]
  [(∈ any_0 any_1) #f])

;; If there are multiple arrows, we (arbitrarily) take the first arity.
(define-metafunction λcρ
  arity : PROC -> number or #f
  
  [(arity (-- (clos OP1 ρ) C ...)) 1]
  [(arity (-- (clos OP2 ρ) C ...)) 2]  
  
  [(arity (-- (clos (λ X (X_0 ...) EXP) ρ) C ...))
   ,(length (term (X_0 ...)))]
  [(arity (-- (clos (λ (X ...) EXP) ρ) C ...))
   ,(length (term (X ...)))]
  ;; ABSTRACT VALUES
  #|
  [(arity (-- (C_0 ... -> C_1) C ...))
   ,(length (term (C_0 ...)))]
  [(arity (-- (C_0 ... -> (λ (x ...) C_1)) C ...))
   ,(length (term (C_0 ...)))]
  [(arity (-- C)) #f]
  [(arity (-- C_0 C ...))
   (arity (-- C ...))]
  |#
  [(arity ((C ... --> any) <= LAB_0 LAB_1 V_b LAB_2 any_0))
   ,(length (term (C ...)))])
  
(test
 (test-equal (term (arity (-- (clos (λ () x) ())))) 0)
 (test-equal (term (arity (-- (clos (λ (x y z) x) ())))) 3)
 (test-equal (term (arity (-- (clos (λ f (x y z) x) ())))) 3)
 ;; FIXME: uncomment when doing ABSTRACT values
 #;(test-equal (term (arity (-- ((nat/c) (nat/c) -> (nat/c))))) 2)
 #;(test-equal (term (arity (-- ((nat/c) (nat/c) -> (λ (x y) (nat/c)))))) 2)
 #;(test-equal (term (arity (-- (string/c) ((nat/c) (nat/c) -> (nat/c))))) 2)
 #;(test-equal (term (arity (-- (pred procedure? f)))) #f)
 ;; FIXME: add blessed case
 )