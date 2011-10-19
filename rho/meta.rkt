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
  [(plain-δ string? (-- (clos string ρ)) LAB) 
   (-- (clos #t ()))]
  [(plain-δ string? V LAB) 
   (-- (clos #f ()))]
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
  ;; Interpreted different than Racket's `sub1'.
  [(plain-δ sub1 (-- (clos natural ρ) C ...) LAB)
   (-- (clos ,(max 0 (sub1 (term natural))) ()))]
  [(plain-δ natural->natural (-- (clos natural ρ) C ...) LAB)
   (meta-apply natural->natural natural)]
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
  [(plain-δ natural-natural->bool
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

(test 
 (test-equal (term (plain-δ add1 (-- (clos 5 ())) †))
             (term (-- (clos 6 ()))))
 (test-equal (term (plain-δ sub1 (-- (clos 5 ())) †))
             (term (-- (clos 4 ()))))
 (test-equal (term (plain-δ sub1 (-- (clos 0 ())) †))
             (term (-- (clos 0 ())))) 
 (test-equal (term (plain-δ +
                            (-- (clos 3 ()))
                            (-- (clos 3 ()))
                            †))
             (term (-- (clos 6 ()))))
 (test-equal (term (plain-δ string=? 
                            (-- (clos "Hi" ()))
                            (-- (clos "Hi" ()))
                            †))
             (term (-- (clos #t ()))))
 (test-equal (term (plain-δ =
                            (-- (clos 3 ()))
                            (-- (clos 3 ()))
                            †))
             (term (-- (clos #t ()))))
 (test-equal (term (plain-δ = 
                            (-- (clos "Hi" ()))
                            (-- (clos 7 ()))
                            †))
             (term (blame † Λ (-- (clos "Hi" ())) = (-- (clos "Hi" ())))))
 )


(define-metafunction λcρ
  meta-apply : OP any ... -> D
  [(meta-apply OP any ...)
   (-- (clos ,(apply (lift (term OP)) (term (any ...))) ()))])

(define (lift f)
  (define-syntax reflect
    (syntax-rules ()
      [(reflect id ...)
       (case f [(id) id] ...)]))
  (reflect add1 + * = < <= > >=               
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

;; Does this value definitely pass this contract?
(define-metafunction λcρ
  contract-in : C V -> #t or #f
  [(contract-in C (-- any ... C C_1 ...)) #t]  
  [(contract-in C (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V))
   (contract-in C V)]
  [(contract-in ((pred MODREF LAB_2) ρ)
                (-- any ... ((pred MODREF_1 LAB_3) ρ_1) C_1 ...))
   #t
   (where #t (modref=? MODREF MODREF_1))]  
  
  
  [(contract-in ((pred OP LAB) ρ) V)
   (proves V OP)]    
  [(contract-in ((and/c CON_1 CON_2) ρ) V)
   ,(and (term (contract-in (CON_1 ρ) V)) (term (contract-in (CON_2 ρ) V)))]
  [(contract-in ((or/c CON_1 CON_2) ρ) V)
   ,(or (term (contract-in (CON_1 ρ) V)) (term (contract-in (CON_2 ρ) V)))]    
  [(contract-in ((cons/c CON_1 CON_2) ρ) (-- (cons V_1 V_2) C ...))
   ,(and (term (contract-in (CON_1 ρ) V_1)) (term (contract-in (CON_2 ρ) V_2)))]
  ;; FIXME: Add back when ABSTRACT values go in.
  #;
  [(contract-in (cons/c C_1 C_2) AV)
   ,(and (andmap (λ (x) (term (contract-in C_1 ,x))) (term (proj-left AV)))
         (andmap (λ (x) (term (contract-in C_2 ,x))) (term (proj-right AV))))]
  [(contract-in C V) #f]
  )

(test
 (test-equal (term (contract-in ((pred procedure? †) ()) (-- (clos (λ (x) x) ())))) #t)
 (test-equal (term (contract-in ((pred zero? †) ()) (-- (clos 0 ())))) #t)
 (test-equal (term (contract-in ((pred procedure? †) ())
                                ((--> (pred (λ (x) x) †)) () <= f g (-- (clos 0 ())) f (-- (clos (λ (x) x) ())))))
             #t)
 (test-equal (term (contract-in ((pred (prime? ^ f g) †) ()) (-- (clos "a" ()) ((pred (prime? ^ f g) †) ()))))
             #t)
 (test-equal (term (contract-in ((pred (prime? ^ g f) †) ()) (-- (clos "a" ()) ((pred (prime? ^ h f) †) ()))))
             #t)
 (test-equal (term (contract-in ((and/c (pred zero? †) (pred exact-nonnegative-integer? †)) ())
                                (-- (clos 0 ()))))
             #t)
 (test-equal (term (contract-in ((and/c (pred zero? †) (pred exact-nonnegative-integer? †)) ())
                                (-- (clos 1 ()))))
             #f)
 (test-equal (term (contract-in ((or/c (pred zero? †) (pred exact-nonnegative-integer? †)) ())
                                (-- (clos 1 ()))))
             #t)
 (test-equal (term (contract-in ((cons/c (pred zero? †) (pred string? †)) ())
                                (-- (cons (-- (clos 0 ())) (-- (clos "s" ()))))))
             #t)
 (test-equal (term (contract-in ((cons/c (pred zero? †) (pred string? †)) ())
                                (-- (cons (-- (clos 0 ())) (-- (clos 2 ()))))))
             #f))






;; Does OP hold on all values abstracted by V
;; [Gives an approximate answer: #f means "failed to prove"]
(define-metafunction λcρ
  proves : V OP -> #t or #f
  [(proves (-- PREVAL C ...) OP)
   #t
   (where TRUE (plain-δ OP (-- PREVAL C ...) ★))]
  ;; FIXME: Add when ABSTRACT values go in.
  #;
  [(proves (-- C_0 ... C C_1 ...) OP)
   #t
   (where #t (proves-con C OP))]  
  [(proves (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) OP)
   (proves V OP)] 
  [(proves V OP) #f])

(test
 (test-equal (term (proves (-- (clos "Hi" ())) string?)) #t)
 (test-equal (term (proves ((--> (pred (λ (x) #t) f)) () <= f g 
                                                      (-- (clos 0 ())) h 
                                                      (-- (clos (λ (x) x) ())))
                           procedure?))
             #t)
 ;; FIXME: Add when ABSTRACT values go in.
 #;
 (test-equal (term (proves ((--> (pred (λ (x) #t) f)) () <= f g 
                                                      (-- (clos 0 ())) h 
                                                      (-- (pred procedure? Λ)))
                           procedure?))
             #t))

(define-metafunction λcρ
  modref=? : MODREF MODREF -> #t or #f
  [(modref=? (X ^ LAB_1 X_1) (X ^ LAB_2 X_1)) #t]
  [(modref=? MODREF MODREF_1) #f])

;; modulename x valuename x modules -> value
(define-metafunction λc-user
  lookup-modref/val : X X (MOD ...) -> VAL ;or bullet
  [(lookup-modref/val X X_1 (MOD ... 
                             (module X LANG REQ STRUCT ... DEF ... (define X_1 any_result) DEF_1 ... any_p)
                             MOD_1 ...))
   any_result]
  [(lookup-modref/val X X_1 any)
   ,(format "unbound module variable ~a from ~a" (term X_1) (term X))])
          
;; modulename x valuename x modules -> contract
(define-metafunction λc-user
  lookup-modref/con : X X (MOD ...) -> CON
  [(lookup-modref/con X X_1 (MOD ... 
                             (module X LANG REQ STRUCT ... DEF ... 
                               (provide/contract any_1 ... [X_1 CON] any_2 ...))
                             MOD_1 ...))
   CON]
  [(lookup-modref/con X X_1 any)
   (pred (λ (x) ,(format "contract for unbound module variable ~a from ~a" (term X_1) (term X))) ★)])
   
(test
 (define Ms 
   (term [(module m racket (require) (define f 1) (provide/contract [f (pred string? m)]))]))
 (test-equal (term (lookup-modref/val m f ,Ms)) 1)
 (test-equal (term (lookup-modref/val m g ,Ms)) "unbound module variable g from m")
 (test-equal (term (lookup-modref/con m f ,Ms)) (term (pred string? m)))
 (test-equal (term (lookup-modref/con m g ,Ms)) 
             (term (pred (λ (x) "contract for unbound module variable g from m") ★))))
 
 

