#lang racket
;; A reformulation of the language as a calculus of explicit substitutions.

(require redex/reduction-semantics "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test lang)

(define-language λc-user
  ;; Annotated language
  ;; This is just static syntax, no semantic notions at all.
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Programs
  (PROG (MOD ... REQ EXP))
  (MOD (module X LANG REQ STRUCT ... DEF ... PROV))
  (PROV (provide/contract [X PCON] ...))         
  (REQ (require (only-in X X ...) ...))
  (LANG racket racket/base)
  (STRUCT (struct X (X ...)))
  (DEF (define X VAL)
       (define X •))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Expressions  
  (EXP VAL X MODREF 
       (@ EXP EXP ... LAB) 
       (if EXP EXP EXP)
       (let ((X EXP) ...) EXP)
       (begin EXP EXP))
  (MODREF (X ^ LAB X)) ;; X_1 is occurs in LAB and is defined in X_2.
  (LAB X †) ;; † is top-level  
  ((F X) variable-not-otherwise-mentioned)  
    
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Values (syntactic)  
  (VAL natural #t #f string empty 
       LAM OP 
       #;(cons VAL VAL) 
       #;(struct X VAL ...))      
  (LAM (λ (X ...) EXP)
       (λ X (X ...) EXP))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Contracts
  (PCON  (side-condition (name c CON) (term (valid? c)))) 
  (FLAT (side-condition (name c CON) (term (flat? c))))
  (HOC  (side-condition (name c CON) (not (term (flat? c)))))
  (PREDV LAM MODREF OP)
  (CON X
       (pred PREDV LAB) 
       (rec/c X CON)       
       (cons/c CON CON) 
       (and/c CON CON)
       (or/c CON CON)
       (CON ... -> CON)
       (CON ..._1 -> (λ (X ..._1) CON)))
    
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Operations (syntactic)
  (OP car cdr add1 sub1
      zero? procedure? empty? cons? 
      exact-nonnegative-integer? string? boolean? false?
      + - * expt
      = < <= > >=             
      cons 
      string=? string<? string<=? string>? string>=? 
      string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?
      procedure-arity-includes?))


(define-extended-language λcρ λc-user
  ;; Environments
  (ρ ((X V) ...))
  
  ;; Closures
  (D (clos EXP ρ)
     V
     MODREF 
     (@ D D ... LAB)     
     (if D D D)
     (let ((X D) ...) (clos EXP ρ))
     (begin D (clos EXP ρ))
     (CON ρ <= LAB LAB V X D)
     BLAME)    
  
  ;; Note, both
  ;; (-- (cons 1 2)) and (-- (cons (-- (clos 1 ())) (-- (clos 2 ()))))
  ;; are values.
  
  ;; Values (semantic)
  (PREVAL (clos VAL ρ)
          (cons V V)
          (struct X V))
  ((V U) (-- PREVAL C* ...) AV BLESSED)
  (AV (-- C* ...))
  (A V BLAME)
  
  ;; Types of values
  (PROC (-- (clos LAM ρ) C* ...) 
        (-- (clos OP ρ) C* ...)
        (-- C* ...) ;; FIXME: could be more restrictive
        BLESSED)  
        
        
  (BLESSED (BARROW ρ <= LAB LAB V LAB PROC)
           (BARROW ρ <= LAB LAB V LAB BLESSED))
    
  (BARROW (CON ... --> CON)
          (CON ..._1 --> (λ (X ..._1) CON)))
          
  (CARROW (CON ... -> CON)
          (CON ..._1 -> (λ (X ..._1) CON)))
  
  (C  (CON ρ))
  (C* (FLAT* ρ) (HOC* ρ))
    
  (FLAT* (pred PREDV LAB) 
         (cons/c FLAT FLAT) 
         (or/c FLAT FLAT) 
         (rec/c X FLAT))
  (HOC* (CON ... -> CON)
        (CON ..._1 -> (λ (X ..._1) CON))
        (or/c FLAT HOC)
        (cons/c HOC CON) (cons/c CON HOC)
        (rec/c X HOC))
  
  (BLAME (blame LAB LAB V C V)
         (blame LAB LAB V OP V)
         (blame LAB LAB V λ V))
      
  (LAB .... ★ Λ) ; ★ is demonic generated, Λ is language generated
  
  (𝓔 hole 
     (@ V ... 𝓔 D ... LAB)
     (if 𝓔 D D) 
     (let ((X V) ... (X 𝓔) (X D) ...) D)
     (begin 𝓔 D)
     (CON ρ <= LAB LAB V LAB 𝓔))
  
  ;; Conveniences
  (OP1 car cdr add1 sub1
       zero? procedure? empty? cons? 
       exact-nonnegative-integer? string? boolean? false?)
  (OP2 + - * expt
       = < <= > >=             
       cons 
       string=? string<? string<=? string>? string>=? 
       string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?
       procedure-arity-includes?)
  
  (natural->natural add1 sub1)
  (natural-natural->natural + - * expt)
  (natural-natural->bool = < <= > >=)  
  (string-string->bool string=? string<? string>? string<=? string>=?
                       string-ci=? string-ci<? string-ci>? string-ci<=? string-ci>=?)
  
  (bool #t #f)
  (TRUE (-- (clos #t ρ) C* ...))
  (FALSE (-- (clos #f ρ) C* ...))
  
  ) 

;; A valid provide contract is closed and has the or/c invariant.
(define-metafunction λc-user
  valid? : CON -> #t or #f
  [(valid? X) #f]
  [(valid? (pred PREDV any)) #t]
  [(valid? (rec/c X CON))
   (valid? (subst/μ X (subst/μ X (pred string? f) CON) CON))]
  [(valid? (cons/c CON_1 CON_2))
   ,(and (term (valid? CON_1))
         (term (valid? CON_2)))]
  [(valid? (and/c CON_1 CON_2))
   ,(and (term (valid? CON_1))
         (term (valid? CON_2)))]  
  [(valid? (or/c CON_1 CON_2))
   ,(and (term (valid? CON_1))
         (term (flat? CON_1))
         (term (valid? CON_2)))]
  [(valid? (CON_1 ... -> CON_2))
   ,(andmap values (term ((valid? CON_1) ... (valid? CON_2))))]
  [(valid? (CON_1 ... -> (λ (X ...) CON_2)))
   ,(andmap values (term ((valid? CON_1) ... (valid? CON_2))))])

;; A flat contract can be checked immediately.
(define-metafunction λc-user
  flat? : CON -> #t or #f
  [(flat? X) #t]
  [(flat? (pred PREDV any)) #t]
  [(flat? (rec/c X CON)) (flat? CON)]
  [(flat? (cons/c CON_1 CON_2))
   ,(and (term (flat? CON_1))
         (term (flat? CON_2)))]
  [(flat? (and/c CON_1 CON_2))
   ,(and (term (flat? CON_1))
         (term (flat? CON_2)))]  
  [(flat? (or/c CON_1 CON_2))
   ,(and (term (flat? CON_1))
         (term (flat? CON_2)))]
  [(flat? (CON ... -> any)) #f])

(define-metafunction λc-user
  subst/μ : X CON CON -> CON
  [(subst/μ X CON X) CON]
  [(subst/μ X CON X_0) X_0]
  [(subst/μ X CON (and/c CON_0 CON_1))
   (and/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]
  [(subst/μ X CON (or/c CON_0 CON_1))
   (or/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]
  [(subst/μ X CON (cons/c CON_0 CON_1))
   (cons/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]  
  [(subst/μ X CON (rec/c X CON_1))
   (rec/c X CON_1)]
  [(subst/μ X CON (rec/c X_1 CON_1))
   (rec/c X_1 (subst/μ X CON CON_1))]  
  [(subst/μ X CON (CON_1 ... -> CON_2))
   ((subst/μ X CON CON_1) ... -> (subst/μ X CON CON_2))]  
  [(subst/μ X CON (CON_1 ... -> (λ (X_1 ...) CON_2))) ; distinct class of variables
   ((subst/μ X CON CON_1) ... -> (λ (X_1 ...) (subst/μ X CON CON_2)))]   
  [(subst/μ X CON (pred any any_0))
   (pred any any_0)])


(test
 ;; totality test
 (redex-check λcρ (X PCON_1 PCON_2) (term (subst/μ X PCON_1 PCON_2))))


;; https://github.com/samth/var/issues/3
(test 
 (define CON? (redex-match λcρ CON))
 (define PCON? (redex-match λcρ PCON))
 (test-predicate (negate PCON?) (term (rec/c X (or/c (cons/c X X) (-> (pred string? †))))))           
 (test-predicate CON? (term (rec/c X (or/c (cons/c X X) (-> (pred string? †))))))            
 (test-predicate CON? (term X))
 (test-predicate (negate PCON?) (term X)))
 

