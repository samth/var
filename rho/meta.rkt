#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "meta-misc.rkt")
(provide (except-out (all-defined-out) test))
(provide (all-from-out "meta-misc.rkt"))
(test-suite test meta)

(define-metafunction λcρ
  demonic* : CON V -> D
  [(demonic* CON V)
   (-- (clos 0 (env)))
   (where #t (no-behavior V))]
  [(demonic* CON V) 
   (@ (demonic CON) V ★)
   #;(side-condition (printf "demonic ~a\n" (term CON)))])

(test
 (test-equal (term (demonic* (pred boolean? †) (-- (clos 4 (env)))))
             (term (-- (clos 0 (env)))))
 (test-equal (term (demonic* (-> (pred string? †)) (-- (clos (λ () "x") (env)))))
             (term (@ (demonic (-> (pred string? †)))
                      (-- (clos (λ () "x") (env)))
                      ★))))

;; FIXME make syntactic.  Would like to get rid of environment 
;; so that this plays nice with machine.  To do that, have to
;; be able to embed abstract values in syntax.  OK, except for the 
;; environment of predicates---but are these ever needed!?

;; Produce a function that will do "everything" it can
;; to its argument while treating it as a C.
;; The only important part is that functions are applied
;; to all possible values.  Note that this requires traversing
;; pairs.
;; NOTE the environment of a contract is irrelevant.
(define-metafunction λcρ
  demonic : CON -> V
  [(demonic (pred ATOM? LAB)) (-- (clos (λ (x) #t) (env)))]
  
  ;; FIXME: I don't think we're doing the right thing here in terms
  ;; of arity.  And I worry about what to do with things that have unknown arity.
  ;; FIXME: Need to handle structs, too.
  [(demonic (pred PREDV any)) ;; MAYBE improve me: special case o?
   (-- (clos 
        (λ f (x) 
          (if (@ procedure? x Λ)
              (@ f (@ x • ★) ★)  ;; want to add fact that x is a proc.
              (if (@ cons? x Λ)
                  (if •
                      (@ f (@ car x ★) ★)
                      (@ f (@ cdr x ★) ★))
                  #t)))
        (env)))]
  
  [(demonic (and/c CON_0 CON_1)) ;; this is overly conservative, but not clear how to do better
   (-- (clos (λ (x) (begin (@ D1 x Λ)
                           (@ D2 x Λ)))
             (env (D1 (demonic CON_0))
                  (D2 (demonic CON_1)))))]
  
  [(demonic (cons/c CON_0 CON_1))
   (-- (clos (λ (x) (begin (@ D1 (@ car x ★) Λ)
                           (@ D2 (@ cdr x ★) Λ)))
             (env (D1 (demonic CON_0))
                  (D2 (demonic CON_1)))))]
  
  [(demonic (or/c CON_0 CON_1))
   (-- (clos (λ (x) (begin (@ D1 x Λ)
                           (@ D2 x Λ)))
             (env (D1 (demonic CON_0))
                  (D2 (demonic CON_1)))))]  ;; Always safe, hard to do better.
   
  [(demonic (rec/c X CON))
   (demonic CON)]
  
  [(demonic X)
   (demonic (∧))] ;; Safe.  What else could you do?
  
  [(demonic (not/c CON))
   (demonic (∧))]  ;; Safe.  What else could you do?
  
  [(demonic (CON_0 ... -> CON_1))
   (-- (clos (λ (f) (@ D1 (@ f X ... ★) Λ))
             (env (X (-- (CON_0 (env)))) ...  ;; FIXME not the right env -- need to be given env.
                  (D1 (demonic CON_1)))))
   (where (X ...) ,(gen-xs (term (CON_0 ...))))]
   
  [(demonic (CON_0 ... -> (λ (X_0 ...) CON_1)))
   ;; NOTE: Since the environment of a CON plays no role in demonic,
   ;; we do not do extend the environment of CON_1 with ((X_0 (-- CON_0)) ...).
   (-- (clos (λ (f) (@ D1 (@ f X ... ★) Λ))
             (env (X (-- (CON_0 (env)))) ...   ;; FIXME not the right env -- need to be given env.
                  (D1 (demonic CON_1)))))
   (where (X ...) ,(gen-xs (term (CON_0 ...))))])

(test
 (test-equal (term (demonic (∧)))
             (term (-- (clos
                        (λ f (x) 
                          (if (@ procedure? x Λ)
                              (@ f (@ x • ★) ★)
                              (if (@ cons? x Λ)
                                  (if •
                                      (@ f (@ car x ★) ★)
                                      (@ f (@ cdr x ★) ★))
                                  #t)))
                        (env)))))
 
 (test-equal (term (demonic (and/c (∧) (∧))))
             (term (-- (clos (λ (x) (begin (@ D1 x Λ)
                                           (@ D2 x Λ)))
                             (env (D1 (demonic (∧)))
                                  (D2 (demonic (∧))))))))
 
 (test-equal (term (demonic (cons/c (∧) (∧))))
             (term (-- (clos (λ (x) (begin (@ D1 (@ car x ★) Λ)
                                           (@ D2 (@ cdr x ★) Λ)))
                             (env (D1 (demonic (∧)))
                                  (D2 (demonic (∧))))))))
 
 (test-equal (term (demonic (or/c (∧) (∧))))
             (term (-- (clos (λ (x) (begin (@ D1 x Λ)
                                           (@ D2 x Λ)))
                             (env (D1 (demonic (∧)))
                                  (D2 (demonic (∧))))))))
 
 (test-equal (term (demonic (not/c (∧))))
             (term (demonic (∧))))
   
 (test-equal (term (demonic (rec/c X (∧))))
             (term (demonic (∧))))
 
 (test-equal (term (demonic ((∧) -> (∧))))              
             (term (-- (clos (λ (f) (@ D1 (@ f x0 ★) Λ))
                             (env (x0 (-- ((∧) (env))))
                                  (D1 (demonic (∧))))))))
 
 (test-equal (term (demonic ((∧) -> (λ (x) (∧)))))
             (term (-- (clos (λ (f) (@ D1 (@ f x0 ★) Λ))
                             (env (x0 (-- ((∧) (env))))
                                  (D1 (demonic (∧)))))))))
 
;; Rather than use gensym here, we deterministically generate 
;; names x0, x1, ..., xi.  Since this function is applied to
;; lists of CONs appearing in `->' contracts, which there are
;; only finitely many, this function does not generate infinite xs.
;; [Probably want to tune up to increase precision at some point.]
(define (gen-xs ls)
  (for/list ([c (in-list ls)]
             [i (in-naturals)])
    (string->symbol (format "x~a" i))))

(test
 (test-equal (gen-xs (list 'a 'b 'c))
             (list 'x0 'x1 'x2)))

(define-metafunction λcρ
  no-behavior : V -> #t or #f
  [(no-behavior blessed-AV) #f]
  [(no-behavior blessed-A) #f]
  [(no-behavior AV) #t]
  [(no-behavior (-- (clos natural ρ) any ...)) #t]
  [(no-behavior (-- (clos bool ρ) any ...)) #t]
  [(no-behavior (-- (clos string ρ) any ...)) #t]
  [(no-behavior (-- (clos empty ρ) any ...)) #t]
  [(no-behavior (-- (cons V_1 V_2) any ...))
   ,(and (term (no-behavior V_1))
         (term (no-behavior V_2)))]
  [(no-behavior (-- (struct X_m X_tag V_1 ...) any ...))
   #t
   (where (#t ...) ((no-behavior V_1) ...))]
  [(no-behavior V) #f])

(test
 (test-equal (term (no-behavior (-- (clos #f (env))))) #t) 
 (test-equal (term (no-behavior (-- ((pred boolean? †) (env))))) #t)
 (test-equal (term (no-behavior (-- (clos (λ (x) #t) (env))))) #f)
 (test-equal (term (no-behavior (-- (cons (-- (clos 0 (env)))
                                          (-- (clos 1 (env)))))))
             #t)
 (test-equal (term (no-behavior (-- (cons (-- (clos 0 (env)))
                                          (-- (clos (λ (x) #t) (env)))))))
             #f)
 (test-equal (term (no-behavior (-- (struct p posn
                                      (-- (clos 0 (env)))
                                      (-- (clos 1 (env)))))))
             #t)
 (test-equal (term (no-behavior (-- (struct p posn
                                      (-- (clos 0 (env)))
                                      (-- (clos (λ (x) #t) (env)))))))
             #f))

 

(define-metafunction λcρ
  amb : D D ... -> D
  [(amb D) D]
  [(amb D_1 D_3 ...)
   (if (-- ((pred (λ (x) #t) Λ) (env))) D_1 (amb D_3 ...))])

(define-metafunction λcρ
  amb/e : EXP EXP ... -> EXP
  [(amb/e EXP) EXP]
  [(amb/e EXP_1 EXP_3 ...)
   (if • EXP_1 (amb/e EXP_3 ...))])

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
  [(δ cons V_0 V_1 LAB) ; cons works same for concrete and abstract
   ((-- (cons V_0 V_1)))]  
  [(δ (s-cons X_m X_tag natural) V ... LAB)
   ((-- (struct X_m X_tag V ...)))
   (side-condition (= (length (term (V ...))) (term natural)))]  
  [(δ OP V_1 ... AV V_2 ... LAB)
   (abs-δ OP V_1 ... AV V_2 ... LAB)]  
  [(δ OP V ... LAB) 
   ((plain-δ OP V ... LAB))])

(define-metafunction λcρ
  abs-δ : OP V ... AV V ... LAB -> (A ...)
  ;; FIXME holdover from old model
  #;
  [(abstract-δ op V_0 ... V V_1 ... ℓ)
   ((-- #f)) ;; V is impossible, so why not?
   (where #t (impossible? V))]
  
  ;; O? 
  [(abs-δ OP? AV LAB)
   ((-- (clos #t (env)))
    (-- (clos #f (env))))
   (where #t (proves AV OP?))
   (where #t (refutes AV OP?))]
  [(abs-δ OP? AV LAB)
   ((-- (clos #t (env))))
   (where #t (proves AV OP?))]
  [(abs-δ OP? AV LAB)
   ((-- (clos #f (env))))
   (where #t (refutes AV OP?))]
  [(abs-δ OP? AV LAB)
   ((-- (clos #t (env)))
    (-- (clos #f (env))))]
  
  ;; procedure-arity-includes?
  [(abs-δ procedure-arity-includes? (-- PREVAL C ...) AV LAB)
   ((-- (clos #t (env))) 
    (-- (clos #f (env))))
   (where #t (proves AV exact-nonnegative-integer?))]  
  [(abs-δ procedure-arity-includes? AV (-- (clos natural ρ) C ...) LAB)
   ((-- (clos #t (env)))
    (-- (clos #f (env))))
   (where #t (proves AV procedure?))
   (where #f (arity AV))]  
  [(abs-δ procedure-arity-includes? AV (-- (clos natural ρ) C ...) LAB)
   ((-- (clos bool (env))))   
   (where natural_a (arity AV))
   (where bool ,(= (term natural) (term natural_a)))]
  [(abs-δ procedure-arity-includes? V_0 V_1 LAB)
   ((-- (clos #t (env)))
    (-- (clos #f (env))))
   (where #t (proves V_0 procedure?))
   (where #t (proves V_1 exact-nonnegative-integer?))]
  [(abs-δ procedure-arity-includes? V_0 V_1 LAB)
   ((blame LAB Λ V_0 procedure-arity-includes? V_0))
   (where #t (refutes V_0 procedure?))]
  [(abs-δ procedure-arity-includes? V_0 V_1 LAB)
   ((blame LAB Λ V_1 procedure-arity-includes? V_1))
   (where #t (proves V_0 procedure?))
   (where #t (refutes V_1 exact-nonnegative-integer?))]
  [(abs-δ procedure-arity-includes? V_0 V_1 LAB)
   ((-- (clos #t (env)))
    (-- (clos #f (env)))
    (blame LAB Λ V_0 procedure-arity-includes? V_0)
    (blame LAB Λ V_1 procedure-arity-includes? V_1))]
 
  ;; natural->natural
  [(abs-δ natural->natural V LAB)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))
   (where #t (proves V exact-nonnegative-integer?))]
  [(abs-δ natural->natural V LAB)
   ((blame LAB Λ V natural->natural V))
   (where #t (refutes V exact-nonnegative-integer?))]
  [(abs-δ natural->natural V LAB)
   ((-- ((pred exact-nonnegative-integer? Λ) (env)))
    (blame LAB Λ V natural->natural V))]
  
  [(abs-δ quotient V_1 V_2 LAB)
   ((blame LAB Λ V_2 quotient V_2))
   (where #t (proves V_1 exact-nonnegative-integer?))
   (where #t (proves V_2 zero?))]  
  [(abs-δ quotient V_1 V_2 LAB)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))
   (where #t (proves V_1 exact-nonnegative-integer?))
   (where #t (proves V_2 exact-nonnegative-integer?))
   (where #t (refutes V_2 exact-non-negative-integer?))]
  [(abs-δ quotient V_1 V_2 LAB)
   ((-- ((pred exact-nonnegative-integer? Λ) (env)))
    ((blame LAB Λ V_1 quotient V_1)
    (blame LAB Λ V_2 quotient V_2)))]  
  
  ;; natural-natural->natural
  [(abs-δ natural-natural->natural V_1 V_2 LAB)
   ((blame LAB Λ V_1 natural-natural->natural V_1))
   (where #t (refutes V_1 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->natural V_1 V_2 LAB)
   ((blame LAB Λ V_2 natural-natural->natural V_2))
   (where #t (proves V_1 exact-nonnegative-integer?))
   (where #t (refutes V_2 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->natural V_1 V_2 LAB)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))
   (where #t (proves V_1 exact-nonnegative-integer?))
   (where #t (proves V_2 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->natural V_1 V_2 LAB)
   ((-- ((pred exact-nonnegative-integer? Λ) (env)))
    (blame LAB Λ V_2 natural-natural->natural V_2))
   (where #t (proves V_1 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->natural V_1 V_2 LAB)
   ((-- ((pred exact-nonnegative-integer? Λ) (env)))
    (blame LAB Λ V_1 natural-natural->natural V_1))
   (where #t (proves V_2 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->natural V_1 V_2 LAB)
   ((-- ((pred exact-nonnegative-integer? Λ) (env)))
    (blame LAB Λ V_1 natural-natural->natural V_1)
    (blame LAB Λ V_2 natural-natural->natural V_2))]
  
  ;; natural-natural->bool
  [(abs-δ natural-natural->bool V_1 V_2 LAB)
   ((blame LAB Λ V_1 natural-natural->bool V_1))
   (where #t (refutes V_1 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->bool V_1 V_2 LAB)
   ((blame LAB Λ V_2 natural-natural->bool V_2))
   (where #t (proves V_1 exact-nonnegative-integer?))
   (where #t (refutes V_2 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->bool V_1 V_2 LAB)
   ((-- ((pred boolean? Λ) (env))))
   (where #t (proves V_1 exact-nonnegative-integer?))
   (where #t (proves V_2 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->bool V_1 V_2 LAB)
   ((-- ((pred boolean? Λ) (env)))
    (blame LAB Λ V_2 natural-natural->bool V_2))
   (where #t (proves V_1 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->bool V_1 V_2 LAB)
   ((-- ((pred boolean? Λ) (env)))
    (blame LAB Λ V_1 natural-natural->bool V_1))
   (where #t (proves V_2 exact-nonnegative-integer?))]
  [(abs-δ natural-natural->bool V_1 V_2 LAB)
   ((-- ((pred boolean? Λ) (env)))
    (blame LAB Λ V_1 natural-natural->bool V_1)
    (blame LAB Λ V_2 natural-natural->bool V_2))]
   
  ;; string-string->string
  [(abs-δ string-string->bool V_1 V_2 LAB)
   ((blame LAB Λ V_1 string-string->bool V_1))
   (where #t (refutes V_1 string?))]
  [(abs-δ string-string->bool V_1 V_2 LAB)
   ((blame LAB Λ V_2 string-string->bool V_2))
   (where #t (proves V_1 string?))
   (where #t (refutes V_2 string?))]
  [(abs-δ string-string->bool V_1 V_2 LAB)
   ((-- ((pred boolean? Λ) (env))))
   (where #t (proves V_1 string?))
   (where #t (proves V_2 string?))]
  [(abs-δ string-string->bool V_1 V_2 LAB)
   ((-- ((pred boolean? Λ) (env)))
    (blame LAB Λ V_2 string-string->bool V_2))
   (where #t (proves V_1 string?))]
  [(abs-δ string-string->bool V_1 V_2 LAB)
   ((-- ((pred boolean? Λ) (env)))
    (blame LAB Λ V_1 string-string->bool V_1))
   (where #t (proves V_2 string?))]
  [(abs-δ string-string->bool V_1 V_2 LAB)
   ((-- ((pred boolean? Λ) (env)))
    (blame LAB Λ V_1 string-string->bool V_1)
    (blame LAB Λ V_2 string-string->bool V_2))]
  
  ;; car
  [(abs-δ car V LAB)
   (proj-left V)
   (where #t (proves V cons?))]
  [(abs-δ car V LAB)
   ((blame LAB Λ V car V))
   (where #t (refutes V cons?))]
  [(abs-δ car V LAB)
   (A ... (blame LAB Λ V car V))
   (where (A ...) (proj-left V))]
  
  ;; cdr
  [(abs-δ cdr V LAB)
   (proj-right V)
   (where #t (proves V cons?))]
  [(abs-δ cdr V LAB)
   ((blame LAB Λ V cdr V))
   (where #t (refutes V cons?))]
  [(abs-δ cdr V LAB)
   (A ... (blame LAB Λ V cdr V))
   (where (A ...) (proj-right V))]
  
  ;; struct ops
  [(abs-δ (s-pred X_m X_tag) AV LAB)
   ((-- (clos #t (env))))
   (where #t (contract-in ((pred ((tag->pred X_tag) ^ Λ X_m) Λ) (env)) AV))]  
  [(abs-δ (s-pred X_m X_tag) AV LAB)
   ((-- (clos #f (env))))
   (where #t (contract-not-in ((pred ((tag->pred X_tag) ^ Λ X_m) Λ) (env)) AV))]  
  [(abs-δ (s-pred X_m X_tag) AV LAB)
   ((-- (clos #t (env)))
    (-- (clos #f (env))))]
   
  [(abs-δ (s-ref X_m X_tag natural) AV LAB)
   ((-- ((∧) (env))))
   (where #t (contract-in ((pred ((tag->pred X_tag) ^ Λ X_m) Λ) (env)) AV))] 
  [(abs-δ (s-ref X_m X_tag natural) AV LAB)
   ((blame LAB Λ AV (s-ref X_m X_tag natural) AV))
   (where #t (contract-not-in ((pred ((tag->pred X_tag) ^ Λ X_m) Λ) (env)) AV))]
  [(abs-δ (s-ref X_m X_tag natural) AV LAB)
   ((-- ((∧) (env)))
    (blame LAB Λ AV (s-ref X_m X_tag natural) AV))])
   
  
(test
 (test-equal (term (δ procedure-arity-includes? (-- ((pred procedure? †) (env))) (-- ((pred exact-nonnegative-integer? †) (env))) f))
             (term ((-- (clos #t (env))) (-- (clos #f (env))))))
 (test-equal (term (δ procedure-arity-includes? (-- ((pred procedure? †) (env))) (-- (clos 3 (env))) f))
             (term ((-- (clos #t (env))) (-- (clos #f (env))))))
 (test-equal (term (δ procedure-arity-includes? (-- ((-> (∧)) (env))) (-- (clos 0 (env))) f))
             (term ((-- (clos #t (env))))))
 (test-equal (term (δ procedure-arity-includes? (-- ((-> (∧)) (env))) (-- (clos 1 (env))) f))
             (term ((-- (clos #f (env))))))
 (test-equal (term (δ procedure-arity-includes? (-- (clos (λ () 0) (env))) (-- ((pred exact-nonnegative-integer? †) (env))) f))
             (term ((-- (clos #t (env))) (-- (clos #f (env))))))
 (test-equal (term (δ add1 (-- ((pred exact-nonnegative-integer? †) (env))) f))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env))))))
 (test-equal (term (δ add1 (-- ((pred string? †) (env))) f))
             (term ((blame f Λ (-- ((pred string? †) (env))) add1 (-- ((pred string? †) (env)))))))
 (test-equal (term (δ add1 (-- ((∧) (env))) f))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env)))
                    (blame f Λ (-- ((∧) (env))) add1 (-- ((∧) (env)))))))
 
 (test-equal (term (δ + (-- (clos 0 (env))) (-- ((pred exact-nonnegative-integer? †) (env))) f))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env))))))
 (test-equal (term (δ + (-- ((pred exact-nonnegative-integer? †) (env))) (-- (clos 0 (env))) f))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env))))))   
 (test-equal (term (δ + (-- ((pred string? †) (env))) (-- (clos 0 (env))) f))
             (term ((blame f Λ (-- ((pred string? †) (env))) + (-- ((pred string? †) (env)))))))
 (test-equal (term (δ + (-- (clos 0 (env))) (-- ((pred string? †) (env))) f))
             (term ((blame f Λ (-- ((pred string? †) (env))) + (-- ((pred string? †) (env)))))))   
 (test-equal (term (δ + (-- (clos 0 (env))) (-- ((∧) (env))) f))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env)))
                    (blame f Λ (-- ((∧) (env))) + (-- ((∧) (env)))))))
 (test-equal (term (δ + (-- ((∧) (env))) (-- (clos 0 (env))) f))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env)))
                    (blame f Λ (-- ((∧) (env))) + (-- ((∧) (env))))))) 
 (test-equal (term (δ + (-- ((pred (p? ^ f g) f) (env))) (-- ((∧) (env))) f))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env)))
                    (blame f Λ (-- ((pred (p? ^ f g) f) (env))) + (-- ((pred (p? ^ f g) f) (env))))
                    (blame f Λ (-- ((∧) (env))) + (-- ((∧) (env)))))))
 
 (test-equal (term (δ string=? (-- (clos "" (env))) (-- ((pred string? †) (env))) f))
             (term ((-- ((pred boolean? Λ) (env))))))
 (test-equal (term (δ string=? (-- ((pred string? †) (env))) (-- (clos "" (env))) f))
             (term ((-- ((pred boolean? Λ) (env))))))   
 (test-equal (term (δ string=? (-- ((pred exact-nonnegative-integer? †) (env))) (-- (clos "" (env))) f))
             (term ((blame f Λ (-- ((pred exact-nonnegative-integer? †) (env))) string=? (-- ((pred exact-nonnegative-integer? †) (env)))))))
 (test-equal (term (δ string=? (-- (clos "" (env))) (-- ((pred exact-nonnegative-integer? †) (env))) f))
             (term ((blame f Λ (-- ((pred exact-nonnegative-integer? †) (env))) string=? (-- ((pred exact-nonnegative-integer? †) (env)))))))   
 (test-equal (term (δ string=? (-- (clos "" (env))) (-- ((∧) (env))) f))
             (term ((-- ((pred boolean? Λ) (env)))
                    (blame f Λ (-- ((∧) (env))) string=? (-- ((∧) (env)))))))
 (test-equal (term (δ string=? (-- ((∧) (env))) (-- (clos "" (env))) f))
             (term ((-- ((pred boolean? Λ) (env)))
                    (blame f Λ (-- ((∧) (env))) string=? (-- ((∧) (env)))))))
 (test-equal (term (δ string=? (-- ((pred (p? ^ f g) f) (env))) (-- ((∧) (env))) f))
             (term ((-- ((pred boolean? Λ) (env)))
                    (blame f Λ (-- ((pred (p? ^ f g) f) (env))) string=? (-- ((pred (p? ^ f g) f) (env))))
                    (blame f Λ (-- ((∧) (env))) string=? (-- ((∧) (env)))))))
 
 (test-equal (term (δ car (-- ((cons/c (pred string? f) (∧)) (env))) f))
             (term ((-- ((pred string? f) (env))))))
 (test-equal (term (δ car (-- ((pred cons? f) (env))) f))
             (term ((-- ((∧) (env))))))
 (test-equal (term (δ car (-- ((pred string? f) (env))) f))
             (term ((blame f Λ (-- ((pred string? f) (env))) car (-- ((pred string? f) (env)))))))
 (test-equal (term (δ car (-- ((∧) (env))) f))
             (term ((-- ((∧) (env)))
                    (blame f Λ (-- ((∧) (env))) car (-- ((∧) (env)))))))
 (test-equal (term (δ cdr (-- ((cons/c (∧) (pred string? f)) (env))) f))
             (term ((-- ((pred string? f) (env))))))
 (test-equal (term (δ cdr (-- ((pred cons? f) (env))) f))
             (term ((-- ((∧) (env))))))
 (test-equal (term (δ cdr (-- ((pred string? f) (env))) f))
             (term ((blame f Λ (-- ((pred string? f) (env))) cdr (-- ((pred string? f) (env)))))))
 (test-equal (term (δ cdr (-- ((∧) (env))) f))
             (term ((-- ((∧) (env)))
                    (blame f Λ (-- ((∧) (env))) cdr (-- ((∧) (env)))))))

 (test-equal (term (abs-δ (s-pred p posn) (-- ((pred (posn? ^ g p) f) (env))) f))
             (term ((-- (clos #t (env))))))
 ;; FIXME fails (returns both #t, #f), but want just #f.
 (test-equal (term (abs-δ (s-pred p posn) (-- ((pred string? f) (env))) f))
             (term ((-- (clos #f (env))))))
 (test-equal (term (abs-δ (s-pred p posn) (-- ((∧) (env))) f))
             (term ((-- (clos #t (env)))
                    (-- (clos #f (env)))))) 
 
 (test-equal (term (abs-δ (s-ref p posn 0) (-- ((pred (posn? ^ g p) f) (env))) f))
             (term ((-- ((∧) (env))))))
 ;; FIXME fails because we don't prove string?s can't be posn?s, but want that.
 (test-equal (term (abs-δ (s-ref p posn 0) (-- ((pred string? f) (env))) f))
             (term ((blame f Λ (-- ((pred string? f) (env))) (s-ref p posn 0) (-- ((pred string? f) (env)))))))
 (test-equal (term (abs-δ (s-ref p posn 0) (-- ((∧) (env))) f))
             (term ((-- ((∧) (env)))
                    (blame f Λ (-- ((∧) (env))) (s-ref p posn 0) (-- ((∧) (env))))))) 
 )
 
 
 

(define-metafunction λcρ
  plain-δ : OP V ... LAB -> A
  [(plain-δ procedure? PROC LAB)
   (-- (clos #t (env)))]
  [(plain-δ procedure? V LAB)
   (-- (clos #f (env)))]
  [(plain-δ string? (-- (clos string ρ)) LAB) 
   (-- (clos #t (env)))]
  [(plain-δ string? V LAB) 
   (-- (clos #f (env)))]
  [(plain-δ boolean? (-- (clos bool ρ) C ...) LAB) 
   (-- (clos #t (env)))]
  [(plain-δ boolean? V LAB) 
   (-- (clos #f (env)))]
  [(plain-δ zero? (-- (clos 0 ρ) C ...) LAB) 
   (-- (clos #t (env)))]
  [(plain-δ zero? (-- (clos natural ρ) C ...) LAB) 
   (-- (clos #f (env)))]  
  [(plain-δ empty? (-- (clos empty ρ) C ...) LAB)
   (-- (clos #t (env)))]
  [(plain-δ empty? V LAB)
   (-- (clos #f (env)))]
  [(plain-δ cons? (-- (cons V_0 V_1) C ...) LAB)
   (-- (clos #t (env)))]    
  [(plain-δ cons? V LAB)
   (-- (clos #f (env)))]  
  [(plain-δ exact-nonnegative-integer? (-- (clos natural ρ) C ...) LAB)
   (-- (clos #t (env)))]
  [(plain-δ exact-nonnegative-integer? V LAB) 
   (-- (clos #f (env)))]  
  [(plain-δ false? (-- (clos #f ρ) C ...) LAB) 
   (-- (clos #t (env)))]
  [(plain-δ false? V LAB) 
   (-- (clos #f (env)))]
  ;; Interpreted different than Racket's `sub1'.
  [(plain-δ sub1 (-- (clos natural ρ) C ...) LAB)
   (-- (clos ,(max 0 (sub1 (term natural))) (env)))]
  [(plain-δ natural->natural (-- (clos natural ρ) C ...) LAB)
   (meta-apply natural->natural natural)]
  [(plain-δ car (-- (cons V_0 V_1) C ...) LAB) V_0]
  [(plain-δ cdr (-- (cons V_0 V_1) C ...) LAB) V_1]
  [(plain-δ procedure-arity-includes? PROC (-- (clos natural ρ) C ...) LAB)
   ;; FIXME: tune up for ABSTRACT values   
   (-- (clos ,(= (term natural) (term (arity PROC))) (env)))]
  ;; Interpreted differently than Racket `-'.
  [(plain-δ -
            (-- (clos natural_1 ρ_1) C_1 ...)
            (-- (clos natural_2 ρ_2) C_2 ...)
            LAB)
   (-- (clos ,(max 0 (- (term natural_1) (term natural_2))) (env)))]
  [(plain-δ quotient
            (-- (clos natural ρ_1) C_1 ...)
            (-- (clos 0 ρ_2) C_2 ...)
            LAB)
   (blame LAB Λ (-- (clos 0 ρ_2) C_2 ...) quotient (-- (clos 0 ρ_2) C_2 ...))]
  [(plain-δ quotient
            (-- (clos natural_1 ρ_1) C_1 ...)
            (-- (clos natural_2 ρ_2) C_2 ...)
            LAB)
   (meta-apply quotient natural_1 natural_2)]
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
  ;; Structs
  [(plain-δ (s-pred X_m X_tag) (-- (struct X_m X_tag V ...) C ...) LAB)
   (-- (clos #t (env)))]
  [(plain-δ (s-pred X_m X_tag) V LAB)
   (-- (clos #f (env)))]
  [(plain-δ (s-ref X_m X_tag natural) (-- (struct X_m X_tag V ...) C ...) LAB)
   V_i
   (where V_i ,(list-ref (term (V ...)) (term natural)))]
  [(plain-δ (s-pred X_m X_tag) (-- (struct X_m X_tag V ...) C ...) LAB)
   (-- (clos #t (env)))]
  [(plain-δ (s-pred X_m X_tag) V LAB)
   (-- (clos #f (env)))]
  [(plain-δ OP V V_1 ... LAB)       ;; catches domain errors
   (blame LAB Λ V OP V)])

(test 
 (test-equal (term (δ cons (-- (clos 0 (env))) (-- (clos 1 (env))) †))
             (term ((-- (cons (-- (clos 0 (env))) (-- (clos 1 (env))))))))
 (test-equal (term (plain-δ add1 (-- (clos 5 (env))) †))
             (term (-- (clos 6 (env)))))
 (test-equal (term (plain-δ sub1 (-- (clos 5 (env))) †))
             (term (-- (clos 4 (env)))))
 (test-equal (term (plain-δ sub1 (-- (clos 0 (env))) †))
             (term (-- (clos 0 (env))))) 
 (test-equal (term (plain-δ +
                            (-- (clos 3 (env)))
                            (-- (clos 3 (env)))
                            †))
             (term (-- (clos 6 (env)))))
 (test-equal (term (plain-δ string=? 
                            (-- (clos "Hi" (env)))
                            (-- (clos "Hi" (env)))
                            †))
             (term (-- (clos #t (env)))))
 (test-equal (term (plain-δ empty? (-- (clos empty #hash())) Λ))
             (term (-- (clos #t (env)))))
 (test-equal (term (plain-δ =
                            (-- (clos 3 (env)))
                            (-- (clos 3 (env)))
                            †))
             (term (-- (clos #t (env)))))
 (test-equal (term (plain-δ = 
                            (-- (clos "Hi" (env)))
                            (-- (clos 7 (env)))
                            †))
             (term (blame † Λ (-- (clos "Hi" (env))) = (-- (clos "Hi" (env))))))
 
 (test-equal (term (plain-δ (s-pred p posn) (-- (struct p posn)) †))
             (term (-- (clos #t (env)))))
 (test-equal (term (plain-δ (s-pred p posn) (-- (struct p blah)) †))
             (term (-- (clos #f (env)))))
 (test-equal (term (plain-δ (s-pred p posn) (-- (clos 0 (env))) †))
             (term (-- (clos #f (env)))))
 (test-equal (term (δ (s-cons p posn 0) †))
             (term ((-- (struct p posn)))))
 (test-equal (term (δ (s-cons p posn 2) (-- (clos 0 (env))) (-- (clos 1 (env))) †))
             (term ((-- (struct p posn (-- (clos 0 (env))) (-- (clos 1 (env))))))))
 (test-equal (term (plain-δ (s-ref p posn 0) (-- (struct p posn (-- (clos 0 (env))) (-- (clos 5 (env))))) †))
             (term (-- (clos 0 (env)))))
 (test-equal (term (plain-δ (s-ref p posn 1) (-- (struct p posn (-- (clos 0 (env))) (-- (clos 5 (env))))) †))
             (term (-- (clos 5 (env)))))
 )


(define-metafunction λcρ
  meta-apply : OP any ... -> D
  [(meta-apply OP any ...)
   (-- (clos ,(apply (lift (term OP)) (term (any ...))) (env)))])

(define (lift f)
  (define-syntax reflect
    (syntax-rules ()
      [(reflect id ...)
       (case f 
         [(id) id] ...
         [else (error 'lift "unknown procedure: ~a" f)])]))
  (reflect add1 + * expt quotient = < <= > >=               
           string=? string<? string>? string<=? string>=?
           string-ci=? string-ci<? string-ci>? string-ci<=? string-ci>=?))

;; Does this value definitely pass this contract?
;; FIXME -- this needs a cached version
(define-metafunction λcρ
  contract-in : C V -> #t or #f
  [(contract-in C (-- any ... C_0 C_1 ...))
   #t
   (where #t (≡C C C_0))]
  [(contract-in C (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V))
   (contract-in C V)]
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
  [(contract-in ((not/c CON_1) ρ) V)
   (contract-not-in (CON_1 ρ) V)]
  [(contract-in ((cons/c CON_1 CON_2) ρ) AV)
   ,(and (andmap (λ (x) (term (contract-in (CON_1 ρ) ,x))) (term (proj-left AV)))
         (andmap (λ (x) (term (contract-in (CON_2 ρ) ,x))) (term (proj-right AV))))] 
  [(contract-in C V) #f])

(test
 (test-equal (term (contract-in ((pred procedure? †) (env))
                                (-- (clos (λ (x) x) (env))))) 
             #t)
 (test-equal (term (contract-in ((pred zero? †) (env))
                                (-- (clos 0 (env))))) 
             #t)
 (test-equal (term (contract-in ((pred procedure? †) (env))
                                ((--> (pred (λ (x) x) †)) (env) <= f g (-- (clos 0 (env))) f (-- (clos (λ (x) x) (env))))))
             #t)
 (test-equal (term (contract-in ((pred (prime? ^ f g) †) (env))
                                (-- (clos "a" (env)) ((pred (prime? ^ f g) †) (env)))))
             #t)
 (test-equal (term (contract-in ((pred (prime? ^ g f) †) (env))
                                (-- (clos "a" (env)) ((pred (prime? ^ h f) †) (env)))))
             #t)
 (test-equal (term (contract-in ((and/c (pred zero? †) (pred exact-nonnegative-integer? †)) (env))
                                (-- (clos 0 (env)))))
             #t)
 (test-equal (term (contract-in ((and/c (pred zero? †) (pred exact-nonnegative-integer? †)) (env))
                                (-- (clos 1 (env)))))
             #f)
 (test-equal (term (contract-in ((or/c (pred zero? †) (pred exact-nonnegative-integer? †)) (env))
                                (-- (clos 1 (env)))))
             #t)
 (test-equal (term (contract-in ((cons/c (pred zero? †) (pred string? †)) (env))
                                (-- (cons (-- (clos 0 (env))) (-- (clos "s" (env)))))))
             #t)
 (test-equal (term (contract-in ((cons/c (pred zero? †) (pred string? †)) (env))
                                (-- (cons (-- (clos 0 (env))) (-- (clos 2 (env)))))))
             #f)
 
 (test-equal (term (contract-in ((not/c (pred cons? †)) (env))
                                (-- (clos 1 (env)))))
             #t)
 
 (test-equal (term (contract-in ((not/c (pred cons? †)) (env))
                                (-- (cons (-- (clos 0 (env))) (-- (clos 2 (env)))))))
             #f)
 ;; We should really get true here, but it requires more work.
 ;; FIXME known to fail; requires caching
 (test-equal (term (contract-in ((rec/c x 
                                        (or/c (pred empty? †)
                                              (cons/c (pred zero? †) x))) 
                                 (env))
                                (-- (cons (-- (clos 0 (env)))
                                          (-- (clos empty (env)))))))
             #t))

;; Does this value *definitely* fail this contract?
(define-metafunction λcρ
  contract-not-in : C V -> #t or #f  
  [(contract-not-in C V)
   (contract-not-in/cache C V ())])

(test
 (test-equal (term (contract-not-in ((pred string? †) (env)) 
                                    (-- (clos 3 (env)))))
             #t)
 (test-equal (term (contract-not-in ((pred string? †) (env)) 
                                    ((--> (pred string? †)) (env) <= f g (-- (clos 0 (env))) f (-- (clos (λ (x) x) (env))))))
             #t)
 (test-equal (term (contract-not-in ((cons/c (pred string? †) (pred zero? †)) (env))
                                    (-- (cons (-- (clos "" (env))) (-- (clos 0 (env)))))))
             #f)
 (test-equal (term (contract-not-in ((cons/c (pred string? †) (pred zero? †)) (env))
                                    (-- (cons (-- (clos "" (env))) (-- (clos 2 (env)))))))
             #t)
 (test-equal (term (contract-not-in ((rec/c x (or/c (pred empty? †) (cons/c (pred string? †) x))) (env))
                                    (-- (clos (λ (x) x) (env)))))
             #t))

(define-metafunction λcρ
  contract-not-in/cache : C V ((C V) ...) -> #t or #f
  [(contract-not-in/cache C V ((C_0 V_0) ... (C V) (C_1 V_1) ...)) #f] ;; FIXME -- use ≡C
  ;; Pretty sure this is not needed
  #;
  [(contract-not-in/cache (CON-INAPPLICABLE ρ) V any)
   #t
   (where #t (proves V procedure?))]
  [(contract-not-in/cache C (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) any)
   (contract-not-in/cache C V any)] 
  [(contract-not-in/cache ((pred OP LAB) ρ) V any)
   (refutes V OP)] 
  ;; FIXME maybe add struct?
  #;
  [(contract-not-in/cache ((pred OP LAB) ρ) V any)
   #f
   (where #t (proves V struct?))
   (side-condition (not (eq? (term OP) 'struct?)))]   
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
  
  [(contract-not-in/cache ((not/c CON_1) ρ) V ((C_3 V_3) ...))
   (contract-in (CON_1 ρ) V)] ;; FIXME -- use contract-not-in/cache when it exists
  
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
  [(proves (-- C_0 ... C C_1 ...) OP)
   #t
   (where #t (proves-con C OP))] 
  [(proves (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) OP)
   (proves V OP)] 
  [(proves V OP) #f])

(test
 (test-equal (term (proves (-- (clos "Hi" (env))) string?)) #t)
 (test-equal (term (proves ((--> (pred (λ (x) #t) f)) (env) <= f g 
                                                      (-- (clos 0 (env))) h 
                                                      (-- (clos (λ (x) x) (env))))
                           procedure?))
             #t) 
 
 (test-equal (term (proves (-- ((pred procedure? Λ) (env)))
                           procedure?))
             #t)
 
 (test-equal (term (proves ((--> (pred (λ (x) #t) f)) 
                            (env) <= f g 
                            (-- (clos 0 (env))) h 
                            (-- ((pred procedure? Λ) (env))))
                           procedure?))
             #t))

;; Does (negate o?) hold on all values abstracted by AV
(define-metafunction λcρ
  refutes : V OP -> #t or #f
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
 (test-equal (term (refutes (-- (clos 0 (env))) empty?)) #t)
 (test-equal (term (refutes (-- (cons (-- (clos 0 (env))) (-- (clos 1 (env))))) cons?)) #f)
 (test-equal (term (refutes (-- (cons (-- (clos 0 (env))) (-- (clos 1 (env))))) string?)) #t)
 (test-equal (term (refutes ((--> (pred string? †)) (env) <= f g (-- (clos 0 (env))) f (-- (clos (λ () 1) (env)))) string?))
             #t)
 (test-equal (term (refutes ((--> (pred string? †)) (env) <= f g (-- (clos 0 (env))) f (-- (clos (λ () 1) (env)))) procedure?))
             #f)
                   
 #;
 (test-equal (term (refutes (-- (cons/c (pred exact-nonnegative-integer? p) (pred exact-nonnegative-integer? p))) cons?)) #f)
 )

;; Does satisfying C imply o?
(define-metafunction λcρ
  proves-con : C OP -> #t or #f  
  [(proves-con ((pred OP_0 LAB) ρ) OP_1)
   (proves-predicate OP_0 OP_1)]  
  [(proves-con ((or/c CON_0 CON_1) ρ) OP)
   ,(and (term (proves-con (CON_0 ρ) OP))
         (term (proves-con (CON_1 ρ) OP)))]
  [(proves-con ((and/c CON_0 CON_1) ρ) OP)
   ,(or (term (proves-con (CON_0 ρ) OP))
        (term (proves-con (CON_1 ρ) OP)))]
  [(proves-con ((not/c CON_0) ρ) OP)
   (refutes-con (CON_0 ρ) OP)]
  [(proves-con ((cons/c CON_0 CON_1) ρ) cons?) #t]
  [(proves-con ((CON_0 ... -> any) ρ) procedure?) #t]
  [(proves-con C OP) #f])

(test
 (test-equal (term (proves-con ((pred procedure? Λ) (env)) procedure?)) #t)
 (test-equal (term (proves-con ((pred procedure? Λ) (env)) string?)) #f)
 (test-equal (term (proves-con ((pred false? †) (env)) boolean?)) #t)
 (test-equal (term (proves-con ((cons/c (pred string? †) (pred boolean? †)) (env))
                               cons?))
             #t)
 (test-equal (term (proves-con ((-> (pred string? †)) (env)) procedure?)) #t)
 (test-equal (term (proves-con ((-> (pred string? †)) (env)) string?)) #f)
 (test-equal (term (proves-con ((and/c (pred boolean? †) (pred false? †)) (env)) false?)) #t)
 (test-equal (term (proves-con ((or/c (pred boolean? †) (pred false? †)) (env)) false?)) #f)
 (test-equal (term (proves-con ((or/c (pred false? †) (pred boolean? †)) (env)) false?)) #f))

 
                   
 

(define-metafunction λcρ
  proves-predicate : OP OP -> #t or #f
  [(proves-predicate OP OP) #t]
  [(proves-predicate zero? exact-nonnegative-integer?) #t]
  [(proves-predicate false? boolean?) #t]
  [(proves-predicate OP_0 OP_1) #f])

;; Does satisfying C imply (negate o?)
(define-metafunction λcρ
  refutes-con : C OP -> #t or #f
  [(refutes-con ((CON_0 ... -> any) ρ) procedure?) #f]
  [(refutes-con ((CON_0 ... -> any) ρ) OP) #t]
  [(refutes-con ((pred OP_0 LAB) ρ) OP_1) 
   (refutes-predicate OP_0 OP_1)]
  [(refutes-con ((or/c CON_0 CON_1) ρ) OP)
   ,(and (term (refutes-con (CON_0 ρ) OP))
         (term (refutes-con (CON_1 ρ) OP)))]
  [(refutes-con ((and/c CON_0 CON_1) ρ) OP)
   ,(or (term (refutes-con (CON_0 ρ) OP))
        (term (refutes-con (CON_1 ρ) OP)))]
  [(refutes-con ((not/c CON_0) ρ) OP)
   (proves-con (CON_0 ρ) OP)]
  [(refutes-con ((cons/c CON_0 CON_1) ρ) OP) 
   #t
   (side-condition (not (eq? (term OP) 'cons?)))]
  [(refutes-con ((rec/c X CON) ρ) OP) 
   ;; Productive implies you'll never get a loop
   (refutes-con ((unroll (rec/c X C)) ρ) OP)]
  [(refutes-con C OP) #f])

(test 
 (test-equal (term (refutes-con ((pred string? f) (env)) exact-nonnegative-integer?))
             #t))

 

(define-metafunction λcρ  
  refutes-predicate : OP OP -> #t or #f
  [(refutes-predicate OP OP) #f]
  [(refutes-predicate empty? OP) #t]
  [(refutes-predicate cons? OP) #t]
  [(refutes-predicate exact-nonnegative-integer? zero?) #f]
  [(refutes-predicate zero? exact-nonnegative-integer?) #f]
  [(refutes-predicate exact-nonnegative-integer? OP) #t]
  [(refutes-predicate zero? OP) #t]
  [(refutes-predicate procedure? OP) #t]
  [(refutes-predicate boolean? false?) #f]
  [(refutes-predicate boolean? OP) #t]
  [(refutes-predicate string? OP) #t]
  [(refutes-predicate false? boolean?) #f]
  [(refutes-predicate false? OP) #t])

;; modulename x valuename x modules -> value
(define-metafunction λcρ
  lookup-modref/val : X X (MOD ...) -> VAL or •
  [(lookup-modref/val X X_1 (MOD ... 
                             (module X LANG REQ STRUCT ... DEF ... (define X_1 any_result) DEF_1 ... 
                               any_p) ;; FIXME should make sure it's provided.
                             MOD_1 ...))
   any_result]
  [(lookup-modref/val X X_1 (MOD ...))
   OP
   (where OP (struct-cons? X X_1 (struct-env (MOD ...))))]
  [(lookup-modref/val X X_1 (MOD ...))
   OP
   (where OP (struct-ref? X X_1 (struct-env (MOD ...))))]
  [(lookup-modref/val X X_1 (MOD ...))
   OP
   (where OP (struct-pred? X X_1 (struct-env (MOD ...))))]
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
 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; structure definitions

(define-metafunction λcρ
  struct-cons? : X X STRUCTENV -> OP or #f
  [(struct-cons? X_def X_cons (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc ...)) any_3 ...) any_1 ...))
   (s-cons X_def X_tag ,(length (term (X_acc ...))))]
  [(struct-cons? X_def X STRUCTENV) #f])

(define-metafunction λcρ
  struct-ref? : X X STRUCTENV -> OP or #f
  [(struct-ref? X_def X_acc (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X ... X_acc X_1 ...)) any_3 ...) any_1 ...))
   (s-ref X_def X_tag ,(length (term (X ...))))]
  [(struct-ref? X_def X STRUCTENV) #f])

(define-metafunction λcρ
  struct-pred? : X X STRUCTENV -> OP or #f
  [(struct-pred? X_def X_pred (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc ...)) any_3 ...) any_1 ...))
   (s-pred X_def X_tag)]
  [(struct-pred? X X_def STRUCTENV) #f])

(define-metafunction λcρ
  struct-env : (MOD ...) -> STRUCTENV
  [(struct-env ((module X_m LANG REQ STRUCT ... DEF ... PROV) ...))
   ((X_m (struct-names STRUCT) ...) ...)])
 
(define-metafunction λcρ
  struct-names : STRUCT -> (X X X (X ...))
  [(struct-names (struct X_tag (X_fld ...)))
   (X_tag (tag->cons X_tag) (tag->pred X_tag) ((fld->acc X_tag X_fld) ...))])

;; Change this if you want constructors and tags to be different.
(define-metafunction λcρ
  tag->cons : X -> X
  [(tag->cons X) X])
(define-metafunction λcρ
  tag->pred : X -> X
  [(tag->pred X) ,(string->symbol (format "~a?" (term X)))])
(define-metafunction λcρ
  fld->acc : X X -> X
  [(fld->acc X_tag X_fld) ,(string->symbol (format "~a-~a" (term X_tag) (term X_fld)))])
        
        
(test
 (test-equal (term (tag->cons posn)) (term posn))
 (test-equal (term (tag->pred posn)) (term posn?))
 (test-equal (term (fld->acc posn x)) (term posn-x))
 (test-equal (term (fld->acc posn y)) (term posn-y))
 
 (test-equal (term (struct-names (struct posn (x y))))                                 
             (term (posn posn posn? (posn-x posn-y))))
 
 (test-equal (term (struct-env [(module p racket
                                  (require)
                                  (struct posn (x y))
                                  (provide/contract))]))
             (term ((p (posn posn posn? (posn-x posn-y)))))))

;; Projections

;; Project an AV to the left
;; (proj-left (-- (cons/c exact-nonnegative-integer? string?) (cons/c zero? string?)))
;; ≡ (-- exact-nonnegative-integer? zero?)
(define-metafunction λcρ
  proj-left : AV -> (V ...)
  [(proj-left (-- C_0 C ...))
   (proj-left/a ((join-contracts)) C_0 C ...)])

(define-metafunction λcρ
  proj-right : AV -> (V ...)
  [(proj-right (-- C_0 C ...))
   (proj-right/a ((join-contracts)) C_0 C ...)])

(define-metafunction λcρ
  proj-left/a : ((-- C ...) ...) C ... -> (V ...)
  [(proj-left/a (AV ...)) (AV ...)]  
  [(proj-left/a (AV ...) ((cons/c CON_0 CON_1) ρ) C_2 ...)
   (proj-left/a (AV_R ...) C_2 ...)
   (where (AV_R ...) 
          ,(for*/list ([av (in-list (term (AV ...)))]
                       [cnew (in-list (term (explode (CON_0 ρ))))])
             (term (remember-contract ,av ,cnew))))]
  [(proj-left/a (AV ...) C_0 C_1 ...)
   (proj-left/a (AV ...) C_1 ...)])

(define-metafunction λcρ
  proj-right/a : ((-- C ...) ...) C ... -> (V ...)
  [(proj-right/a (AV ...)) (AV ...)]  
  [(proj-right/a (AV ...) ((cons/c CON_0 CON_1) ρ) C_2 ...)
   (proj-right/a (AV_R ...) C_2 ...)
   (where (AV_R ...) 
          ,(for*/list ([av (in-list (term (AV ...)))]
                       [cnew (in-list (term (explode (CON_1 ρ))))])
             (term (remember-contract ,av ,cnew))))]
  [(proj-right/a (AV ...) C_0 C_1 ...)
   (proj-right/a (AV ...) C_1 ...)])

(test
 (test-equal (term (proj-left (-- ((∧) (env))
                                  ((cons/c (∧) (or/c (pred exact-nonnegative-integer? f)
                                                     (pred string? f))) (env)))))
             (term ((-- ((∧) (env))))))
 (test-equal (term (proj-right (-- ((∧) (env))
                                   ((cons/c (∧) (or/c (pred exact-nonnegative-integer? f)
                                                      (pred string? f))) (env)))))
             (term ((-- ((pred exact-nonnegative-integer? f) (env)))
                    (-- ((pred string? f) (env)))))))