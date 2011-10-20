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
  (PROV (provide/contract [X CON] ...))         
  (REQ (require (only-in X X ...) ...))
  (LANG racket racket/base)
  (STRUCT (struct X (X ...)))
  (DEF (define X VAL))

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
  (CON FLAT HOC)
  (PRECON X
          (pred PREDV LAB) 
          (rec/c X PRECON)       
          (cons/c PRECON PRECON) 
          (and/c PRECON PRECON)
          (or/c PRECON PRECON)
          (PRECON ... -> PRECON)
          (PRECON ..._1 -> (λ (X ..._1) PRECON)))  
  
  (FLAT (side-condition (name x PRECON) (term (flat? x))))
  (HOC  (side-condition (name x PRECON) (term (not (flat? x)))))  
  (PREDV LAM MODREF OP)
    
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
  ((V U) (-- PREVAL C* ...) BLESSED)
  (A V BLAME)
  
  ;; Types of values
  (PROC (-- (clos LAM ρ) C* ...) 
        (-- (clos OP ρ) C* ...)
        BLESSED)  
        
        
  (BLESSED (BARROW ρ <= LAB LAB V LAB (-- (clos LAM ρ) C* ...))
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
     (begin 𝓔 D))
  
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

;; A flat contract can be checked immediately.
(define-metafunction λc-user
  flat? : PRECON -> #t or #f
  [(flat? X) #t]
  [(flat? (pred PREDV any)) #t]
  [(flat? (rec/c X PRECON)) (flat? PRECON)]
  [(flat? (cons/c PRECON_1 PRECON_2))
   ,(and (term (flat? PRECON_1))
         (term (flat? PRECON_2)))]
  [(flat? (and/c PRECON_1 PRECON_2))
   ,(and (term (flat? PRECON_1))
         (term (flat? PRECON_2)))]  
  [(flat? (or/c CON_1 PRECON_2))
   ,(and (term (flat? PRECON_1))
         (term (flat? PRECON_2)))]
  [(flat? (PRECON ... -> any)) #f])

