#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "meta-misc.rkt")
(provide (except-out (all-defined-out) test))
(provide (all-from-out "meta-misc.rkt"))
(test-suite test meta)

(define-metafunction λcρ
  demonic* : C V -> E
  [(demonic* C V)
   (-- (clos 0 ()))
   (where #t (no-behavior V))]
  [(demonic* C V) (@ (demonic C) V ★)])

;; Produce a function that will do "everything" it can
;; to its argument while treating it as a C.
;; The only important part is that functions are applied
;; to all possible values.  Note that this requires traversing
;; pairs.
;; NOTE the environment of a contract is irrelevant.
(define-metafunction λcρ
  demonic : CON -> V
  [(demonic (pred ATOM? LAB)) (-- (clos (λ (x) #t) ()))]
  
  ;; FIXME: I don't think we're doing the right thing here in terms
  ;; of arity.  And I worry about what to do with things that have unknown arity.
  [(demonic (pred PREDV any)) ;; MAYBE improve me: special case o?
   (-- (clos (λ f (x) 
               (if (@ procedure? x Λ)
                   (@ f (@ x black-hole ★) ★)  ;; want to add fact that x is a proc.
                   (if (@ cons? x Λ)
                       (amb (@ f (@ car x ★) ★)
                            (@ f (@ cdr x ★) ★))
                       #t))))
       ((black-hole (-- (pred (λ (x) #t) ())))))]
  
  [(demonic (and/c CON_0 CON_1))
   (-- (clos (λ (x) (begin (@ (demonic CON_0) x Λ)
                           (@ (demonic CON_1) x Λ)))
             ()))]
  
  [(demonic (cons/c CON_0 CON_1))
   (-- (clos (λ (x) (begin (@ (demonic CON_0) (@ car x ★) Λ)
                           (@ (demonic CON_1) (@ cdr x ★) Λ)))
             ()))]
  
  [(demonic (or/c CON_0 CON_1))
   (demonic (any/c))]  ;; Always safe, hard to do better.
   
  [(demonic (rec/c X CON))
   (demonic (any/c))]  ;; Safe.  What else could you do?
  
  ;; FIXME INFINITY GENSYM
  [(demonic (CON_0 ... -> CON_1))
   (-- (clos (λ (f) (@ (demonic CON_1) (@ f X ... ★) Λ))
             ((X (-- CON_0)) ...)))
   (where f ,(gensym 'f))
   (where (X ...) ,(map (λ _ (gensym 'x)) (term (CON_0 ...))))]
   
  ;; FIXME INFINITY GENSYM
  [(demonic (CON_0 ... -> (λ (X_0 ...) CON_1)))
   ;; NOTE: Since the environment of a CON plays no role in demonic,
   ;; we do not do extend the environment of CON_1 with ((X_0 (-- CON_0)) ...).
   (-- (clos (λ (f) (@ (demonic CON_1) (@ f X ... ★) Λ))
             ((X (-- CON_0)) ...)))
   (where f ,(gensym 'f))
   (where (X ...) ,(map (λ _ (gensym 'x)) (term (CON_0 ...))))])

(define-metafunction λcρ
  no-behavior : V -> #t or #f
  [(no-behavior blessed-AV) #f]
  [(no-behavior blessed-A) #f]
  [(no-behavior AV) #t]
  [(no-behavior (-- nat any ...)) #t]
  [(no-behavior (-- bool any ...)) #t]
  [(no-behavior (-- string any ...)) #t]
  [(no-behavior (-- empty any ...)) #t]
  [(no-behavior (-- (cons V_1 V_2) any ...))
   ,(and (term (no-behavior V_1)) (term (no-behavior V_2)))]
  [(no-behavior V) #f])

(define-metafunction λcρ
  amb : D D ... -> D
  [(amb D) D]
  [(amb D_1 D_2) (if (-- ((pred (λ (x) #t) Λ) ())) D_1 D_2)]
  [(amb D_1 D_2 D_3 ...)
   (amb (if (-- ((pred (λ (x) #t) Λ) ())) D_1 D_2)
        D_3 ...)])

(test
 ;; FIXME Why does this seemingly take FOREVER!?
 #;
 (redex-check λcρ (D_1 D_2) (term (amb D_1 D_2)))
 ;; Must be related to this; looks like a Redex bug:
 ;; EXHAUSTS ALL MEMORY
 #;
 (generate-term λcρ D_1 3))

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
       (case f 
         [(id) id] ...
         [else (error 'lift "unknown procedure: ~a" f)])]))
  (reflect add1 + * expt = < <= > >=               
           string=? string<? string>? string<=? string>=?
           string-ci=? string-ci<? string-ci>? string-ci<=? string-ci>=?))

;; Does this value definitely pass this contract?
(define-metafunction λcρ
  contract-in : C V -> #t or #f
  ;; Wary of syntactic equality and envs.
  ;; Getting this case right is crucial for soundness.
  [(contract-in C (-- any ... C C_1 ...)) #t]
  [(contract-in C (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V))
   (contract-in C V)]
  [(contract-in ((pred MODREF LAB) ρ)
                (-- any ... ((pred MODREF_1 LAB_1) ρ) C_1 ...))
   #t
   (where #t (modref=? MODREF MODREF_1))]    
  [(contract-in ((pred OP LAB) ρ) V)
   (proves V OP)]    
  [(contract-in ((and/c CON_1 CON_2) ρ) V)
   ,(and (term (contract-in (CON_1 ρ) V))
         (term (contract-in (CON_2 ρ) V)))]
  [(contract-in ((or/c CON_1 CON_2) ρ) V)
   ,(or (term (contract-in (CON_1 ρ) V)) 
        (term (contract-in (CON_2 ρ) V)))]
  [(contract-in ((cons/c CON_1 CON_2) ρ) (-- (cons V_1 V_2) C ...))
   ,(and (term (contract-in (CON_1 ρ) V_1)) 
         (term (contract-in (CON_2 ρ) V_2)))]
  ;; FIXME: Add back when ABSTRACT values go in.
  #;
  [(contract-in ((cons/c CON_1 CON_2) ρ) AV)
   ,(and (andmap (λ (x) (term (contract-in (CON_1 ρ) ,x))) (term (proj-left AV)))
         (andmap (λ (x) (term (contract-in (CON_2 ρ) ,x))) (term (proj-right AV))))] 
  [(contract-in C V) #f])

(test
 (test-equal (term (contract-in ((pred procedure? †) ())
                                (-- (clos (λ (x) x) ())))) 
             #t)
 (test-equal (term (contract-in ((pred zero? †) ())
                                (-- (clos 0 ())))) 
             #t)
 (test-equal (term (contract-in ((pred procedure? †) ())
                                ((--> (pred (λ (x) x) †)) () <= f g (-- (clos 0 ())) f (-- (clos (λ (x) x) ())))))
             #t)
 (test-equal (term (contract-in ((pred (prime? ^ f g) †) ())
                                (-- (clos "a" ()) ((pred (prime? ^ f g) †) ()))))
             #t)
 (test-equal (term (contract-in ((pred (prime? ^ g f) †) ())
                                (-- (clos "a" ()) ((pred (prime? ^ h f) †) ()))))
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
             #f)
 ;; We should really get true here, but it requires more work.
 ;; FIXME known to fail
 (test-equal (term (contract-in ((rec/c x 
                                        (or/c (pred empty? †)
                                              (cons/c (pred zero? †) x))) 
                                 ())
                                (-- (cons (-- (clos 0 ()))
                                          (-- (clos empty ()))))))
             #t))

;; Does this value *definitely* fail this contract?
(define-metafunction λcρ
  contract-not-in : C V -> #t or #f  
  [(contract-not-in C V)
   (contract-not-in/cache C V ())])

(test
 (test-equal (term (contract-not-in ((pred string? †) ()) 
                                    (-- (clos 3 ()))))
             #t)
 (test-equal (term (contract-not-in ((pred string? †) ()) 
                                    ((--> (pred string? †)) () <= f g (-- (clos 0 ())) f (-- (clos (λ (x) x) ())))))
             #t)
 (test-equal (term (contract-not-in ((cons/c (pred string? †) (pred zero? †)) ())
                                    (-- (cons (-- (clos "" ())) (-- (clos 0 ()))))))
             #f)
 (test-equal (term (contract-not-in ((cons/c (pred string? †) (pred zero? †)) ())
                                    (-- (cons (-- (clos "" ())) (-- (clos 2 ()))))))
             #t)
 (test-equal (term (contract-not-in ((rec/c x (or/c (pred empty? †) (cons/c (pred string? †) x))) ())
                                    (-- (clos (λ (x) x) ()))))
             #t))

(define-metafunction λcρ
  contract-not-in/cache : C V ((C V) ...) -> #t or #f
  [(contract-not-in/cache C V ((C_0 V_0) ... (C V) (C_1 V_1) ...)) #f]
  ;; Pretty sure this is not needed
  #;
  [(contract-not-in/cache (CON-INAPPLICABLE ρ) V any)
   #t
   (where #t (proves V procedure?))]
  [(contract-not-in/cache C (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) any)
   (contract-not-in/cache C V any)] 
  [(contract-not-in/cache ((pred OP LAB) ρ) V any)
   (refutes V OP)] 
  [(contract-not-in/cache ((cons/c CON_1 CON_2) ρ) V ((C_3 V_3) ...))
   ,(or (term (refutes V cons?)) (term bool_cars) (term bool_cdrs))
   (where (V_car ...) ,(filter (redex-match λcρ V) (term (δ car V ★))))
   (where (V_cdr ...) ,(filter (redex-match λcρ V) (term (δ cdr V ★))))
   (where bool_cars ,(andmap values (term ((contract-not-in/cache (CON_1 ρ) V_car ((((cons/c CON_1 CON_2) ρ) V) (C_3 V_3) ...)) ...))))
   (where bool_cdrs ,(andmap values (term ((contract-not-in/cache (CON_2 ρ) V_cdr ((((cons/c CON_1 CON_2) ρ) V) (C_3 V_3) ...)) ...))))]      
  [(contract-not-in/cache ((and/c CON_1 CON_2) ρ) V ((C_3 V_3) ...))
   ,(or (term (contract-not-in/cache (CON_1 ρ) V ((((and/c CON_1 CON_2) ρ) V) (C_3 V_3) ...)))
        (term (contract-not-in/cache (CON_2 ρ) V ((((and/c CON_1 CON_2) ρ) V) (C_3 V_3) ...))))]
  
  [(contract-not-in/cache ((or/c CON_1 CON_2) ρ) V ((C_3 V_3) ...))
   ,(and (term (contract-not-in/cache (CON_1 ρ) V ((((or/c C_1 C_2) ρ) V) (C_3 V_3) ...)))
         (term (contract-not-in/cache (CON_2 ρ) V ((((or/c C_1 C_2) ρ) V) (C_3 V_3) ...))))]
  
  [(contract-not-in/cache ((rec/c X CON) ρ) V ((C_3 V_3) ...))
   (contract-not-in/cache ((unroll (rec/c X CON)) ρ) V ((((rec/c X CON) ρ) V) (C_3 V_3) ...))
   ;; Can't we just assume this?
   #;
   (where #t (productive? (rec/c x C)))]
                    
  #|
  [(contract-not-in/cache (C_1 ... -> any) V any_1)
   #t
   (where #t (refutes V procedure?))]
    |#
  [(contract-not-in/cache C V any) #f])

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

;; Does (negate o?) hold on all values abstracted by AV
(define-metafunction λcρ
  refutes : V OP -> #t or #f
  ;; FIXME: add back when ABSTRACT
  #;
  [(refutes (-- C_0 ... C C_1 ...) OP) 
   #t
   (where #t (refutes-con C OP))]  
  [(refutes (-- PREVAL C ...) OP)
   #t
   (where FALSE (plain-δ OP (-- PREVAL C ...) ★))]  
  [(refutes (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 any_1) OP)
   #t
   (side-condition (not (eq? 'procedure? (term OP))))]
  [(refutes (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) OP)
   (refutes V OP)]
  [(refutes V OP) #f])

(test
 (test-equal (term (refutes (-- (clos 0 ())) empty?)) #t)
 (test-equal (term (refutes (-- (cons (-- (clos 0 ())) (-- (clos 1 ())))) cons?)) #f)
 (test-equal (term (refutes (-- (cons (-- (clos 0 ())) (-- (clos 1 ())))) string?)) #t)
 (test-equal (term (refutes ((--> (pred string? †)) () <= f g (-- (clos 0 ())) f (-- (clos (λ () 1) ()))) string?))
             #t)
 (test-equal (term (refutes ((--> (pred string? †)) () <= f g (-- (clos 0 ())) f (-- (clos (λ () 1) ()))) procedure?))
             #f)
                   
 #;
 (test-equal (term (refutes (-- (cons/c (pred exact-nonnegative-integer? p) (pred exact-nonnegative-integer? p))) cons?)) #f)
 )



(define-metafunction λcρ
  modref=? : MODREF MODREF -> #t or #f
  [(modref=? (X ^ LAB_1 X_1) (X ^ LAB_2 X_1)) #t]
  [(modref=? MODREF MODREF_1) #f])

;; modulename x valuename x modules -> value
(define-metafunction λc-user
  lookup-modref/val : X X (MOD ...) -> VAL or •
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
 
