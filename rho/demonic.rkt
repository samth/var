#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "meta-misc.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test demon)

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
  demonic : CON -> D
  [(demonic (pred ATOM? LAB)) (-- (clos (λ (x) #t) (env)))]
  [(demonic (atom/c any any_1)) (-- (clos (λ (x) #t) (env)))]
  
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
  
  [(demonic (struct/c X_m X_tag CON ...))
   (-- (clos (λ (x) (begin (@ D EXP_acc Λ) ...))
             (env (D (demonic CON)) ...)))
   (where (EXP_acc ...)
          ,(for/list ([i (length (term (CON ...)))])
             (term (@ (s-ref X_m X_tag ,i) x ★))))
   (where (D ...) ,(gen-xs (term (CON ...))))]
  
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
   (-- (clos (λ (f) (@ D1 (@ f (@ X ★) ... ★) Λ))
             (env   ;; FIXME not the right env -- need to be given env.
              [X (-- ((-> CON_0) (env)))] ... ;; this stupid η expansion is b/c or/c is not a value
              (D1 (demonic CON_1)))))
   (where (X ...) ,(gen-xs (term (CON_0 ...))))]
  
  [(demonic (struct/c X_mod X_tag CON ...))
   (demonic (∧))] ;; FIXME!!
   
  [(demonic (CON_0 ... -> (λ (X_0 ...) CON_1)))
   ;; NOTE: Since the environment of a CON plays no role in demonic,
   ;; we do not do extend the environment of CON_1 with ((X_0 (-- CON_0)) ...).
   (-- (clos (λ (f) (@ D1 (@ f (CON_0 (env) <= ★ Λ (-- (clos "BOGUS" (env))) ★ X) ... ★) Λ))
             (env (X (-- (CON_0* (env)))) ...   ;; FIXME not the right env -- need to be given env.
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