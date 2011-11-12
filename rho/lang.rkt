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
  (EXP VAL X PRIMREF MODREF 
       (@ EXP EXP ... LAB) 
       (if EXP EXP EXP)
       (let ((X EXP) ...) EXP)
       (begin EXP EXP))
  (PRIMREF (PRIM ^ LAB))
  (MODREF (X ^ LAB X)) ;; X_1 occurs in LAB, defined in X_2.
  (LAB X PRIM †) ;; † is top-level  
  ((F X) variable-not-otherwise-mentioned)  
    
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Values (syntactic)  
  (VAL natural boolean character string empty 'variable
       LAM 
       (cons VAL VAL) 
       #;(struct X VAL ...))      
  (LAM (λ (X ...) EXP)
       (λ X (X ...) EXP)
       (λ* (X ... X) EXP))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Contracts
  (PCON  (side-condition (name c CON) (term (valid? c)))) 
  (FLAT (side-condition (name c CON) (term (flat? c))))
  (HOC  (side-condition (name c CON) (not (term (flat? c)))))
  (PREDV LAM MODREF OP)
  (CON X
       (atom/c ATOMLIT LAB)
       (struct/c X X CON ...)
       (pred PREDV LAB) 
       (rec/c X CON)       
       (cons/c CON CON) 
       (and/c CON CON)
       (or/c CON CON)
       (not/c CON) 
       CARROW)
  (CARROW (CON ... -> CON)
          (CON ..._1 -> (λ (X ..._1) CON))
          (CON ... CON ->* CON))
  (ANYCON (pred (λ (X) #t) LAB))
  (ATOMLIT natural
           boolean
           character
           empty
           'variable)
  (boolean #t #f)
  (character (side-condition any_c (char? (term any_c))))
    
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Operations (syntactic)
  (PRIM OP apply values)
  (OP car cdr add1 sub1 random
      zero? procedure? empty? cons? eqv? char?
      exact-nonnegative-integer? string? symbol? boolean? false?
      + - * expt quotient
      = < <= > >=             
      cons 
      symbol=?
      char=? char<? char<=? char>? char>=?
      string=? string<? string<=? string>? string>=? 
      string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?
      procedure-arity-includes?))


(define-extended-language λcρ λc-user
  ;; Environments, stores
  (a (loc any))
  (σ (side-condition any_h (hash? (term any_h))))
  (ρ (side-condition any_h (hash? (term any_h))))
  (S V)
  (STRUCTENV ((X (X X X (X ...)) ...) ...))
  
  (EXP .... PRIM •)
  (VAL .... PRIM)
  
  (OP .... 
      ;struct?
      (s-pred X X)
      (s-cons X X natural)
      (s-ref X X natural))
  
  ;; Closures
  (D (clos EXP ρ)
     V
     MODREF 
     (@ D D ... LAB)     
     (if D D D)
     (let ((X D) ...) (clos EXP ρ))
     (begin D (clos EXP ρ))
     (CON ρ <= LAB LAB V LAB D)
     BLAME)    
  
  ;; Values (semantic)
  (PREVAL (clos VAL ρ)
          (cons V V)
          (struct X X V ...))
  ((V U) (-- PREVAL C* ...) AV BLESSED)
  (AV (-- C* ...))
  (AV* AV BLESSEDAV)
  (A V BLAME)
  
  (STRUCTV (-- (struct X X V ...) C* ...))
  
  ;; Types of values
  (PROC (-- (clos LAM ρ) C* ...) 
        (-- (clos PRIM ρ) C* ...)
        (-- C* ...) ;; FIXME: could be more restrictive
        BLESSED)  
        
        
  (BLESSED (BARROW ρ <= LAB LAB V LAB PROC)
           (BARROW ρ <= LAB LAB V LAB BLESSED))
  
  (BLESSEDAV (BARROW ρ <= LAB LAB V LAB AV)
             (BARROW ρ <= LAB LAB V LAB BLESSEDAV))
    
  (BARROW (CON ... --> CON)
          (CON ..._1 --> (λ (X ..._1) CON))
          (CON ... CON -->* CON))
  
  (C  (CON ρ))
  (C* (FLAT* ρ) (HOC* ρ))
    
  (FLAT* (pred PREDV LAB) 
         (cons/c FLAT FLAT) 
         (struct/c X X FLAT ...)
         (not/c FLAT)
         (atom/c ATOMLIT LAB)
         (or/c FLAT FLAT)
         (rec/c X FLAT))
  (HOC* CARROW       
        (cons/c HOC CON) 
        (cons/c CON HOC)
        (struct/c X X CON ... HOC CON ...)
        (or/c FLAT HOC)
        (rec/c X HOC))
  
  (ATOM? exact-nonnegative-integer?
         boolean?
         zero?
         string?
         symbol?
         empty?
         false?)
  (ATOMC ((pred ATOM? LAB) ρ))
  (CONSC ((pred cons? LAB) ρ)
         ((cons/c CON_1 CON_2) ρ))
  (NOTPROCC ATOMC CONSC)
  
  (BLAME (blame LAB LAB V C V)
         (blame LAB LAB V PRIM V)
         (blame LAB LAB V λ V))
      
  (LAB .... ★ Λ) ; ★ is demonic generated, Λ is language generated
  
  (𝓔 hole 
     (@ V ... 𝓔 D ... LAB)
     (if 𝓔 D D) 
     (let ((X V) ... (X 𝓔) (X D) ...) D)
     (begin 𝓔 D)
     (side-condition (CON_1 ρ <= LAB LAB V LAB 𝓔)
                     (not (redex-match λcρ ANYCON (term CON_1)))))
  
  (REDEX (clos • ρ)
         (clos PRIMREF ρ)
         (clos X ρ)
         (clos (@ any ... LAB) ρ)
         (clos (if any ...) ρ)
         (clos (begin any ...) ρ)
         (clos (let ((X any) ...) EXP) ρ)
         (clos MODREF ρ)
         (@ V V ... LAB)
         (if V D D)
         (begin V D)
         (let ((X V) ...) D)
         PREVAL
         
         MODREF   
         (CON ρ <= LAB LAB any LAB V)
         (ANYCON ρ <= LAB LAB any LAB any)
         BLAME)
  
  ;; Conveniences  
  (OP? zero? procedure? empty? cons? char?
       exact-nonnegative-integer? string? symbol? boolean? false?)
  (OP0* +)
  (OP1 car cdr add1 sub1 random OP?)
  (OP2 + - * expt quotient eqv?
       = < <= > >=             
       cons 
       char=? char<? char<=? char>? char>=?
       symbol=?
       string=? string<? string<=? string>? string>=? 
       string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?
       procedure-arity-includes?)
    
  (natural->natural add1 sub1)
  (char-char->bool char=? char<? char<=? char>? char>=?)
  (natural*->natural +)
  (natural-natural->natural - * expt) ; does not include quotient (partial).
  (natural-natural->bool = < <= > >=)  
  (string-string->bool string=? string<? string>? string<=? string>=?
                       string-ci=? string-ci<? string-ci>? string-ci<=? string-ci>=?)
  
  
  (TRUE (-- (clos #t ρ) C* ...))
  (FALSE (-- (clos #f ρ) C* ...))) 

(define-extended-language λc-raw λc-user
  ;; Raw, unannotated language
  (RP (RMOD ... RREQ REXP))
  
  (RMOD (module X LANG RREQ ... RSTRUCT ... RDEF ...
          (provide/contract [X RCON] ...))
        (module X LANG
          (provide/contract [X RCON] ...))
        (define/contract X RCON RPV)
        (define/contract X RCON bullet))
  
  (MODENV ((X (X ...)) ...))
  (RREQ (require RELEM ...))
  (RELEM X 'X (only-in 'X X ...) (only-in X X ...))
  (RDEF (define X RPV)
        (define (X X ...) REXP)
        (define X bullet))
  (RSTRUCT STRUCT)
    
  (bullet •)
  (RL (λ (X ...) REXP)
      (λ X (X ...) REXP)
      (λ XS-DOT-X REXP))
  
  (XS-DOT-X (side-condition any_xs (improper-formals? (term any_xs))))
      
  (RPV VAL RL)      
  (RSV RL X OP) ; Syntactic values for pred.  
  (REXP RPV X PRIM         
        (REXP REXP ...)
        (cond [REXP REXP] ... [else REXP])
        (if REXP REXP REXP) 
        (PRIM REXP REXP ...) 
        (let ((X REXP) ...) REXP) 
        (begin REXP REXP ...)
        (and REXP ...)
        (or REXP ...))
  
  (RCON OP 
        ATOMLIT
        any/c 
        (pred RSV)        
        (cons/c RCON RCON) 
        (struct/c X RCON ...)
        (or/c RCON RCON) 
        (and/c RCON RCON)          
        (rec/c X RCON)
        (not/c RCON)
        (one-of/c ATOMLIT ATOMLIT ...)
        (symbols 'variable 'variable ...)
        (list/c RCON ...)
        (-> RCON ... RCON)
        (-> RCON ..._1 (λ (X ..._1) RCON))
        (->* (RCON ...) #:rest RCON RCON)
        (listof RCON)
        (non-empty-listof RCON)
        X)
  )

(define (improper-formals? x)
  (or (symbol? x)
      (and (cons? x)
           (symbol? (car x))
           (improper-formals? (cdr x)))))
       

;; A valid provide contract is closed and has the or/c invariant.
(define-metafunction λc-user
  valid? : CON -> #t or #f
  [(valid? X) #f]
  [(valid? (atom/c ATOMLIT any)) #t]
  [(valid? (pred PREDV any)) #t]
  [(valid? (rec/c X CON))
   (valid? (subst/μ X (subst/μ X (pred string? f) CON) CON))]
  [(valid? (cons/c CON_1 CON_2))
   ,(and (term (valid? CON_1))
         (term (valid? CON_2)))]
  [(valid? (struct/c X_1 X_2 CON ...))
   ,(andmap values (term ((valid? CON) ...)))]
  [(valid? (and/c CON_1 CON_2))
   ,(and (term (valid? CON_1))
         (term (valid? CON_2)))]  
  [(valid? (or/c CON_1 CON_2))
   ,(and (term (valid? CON_1))
         (term (flat? CON_1))
         (term (valid? CON_2)))]
  [(valid? (not/c CON)) (flat? CON)]
  [(valid? (CON_1 ... -> CON_2))
   ,(andmap values (term ((valid? CON_1) ... (valid? CON_2))))]
  [(valid? (CON_1 ... -> (λ (X ...) CON_2)))
   ,(andmap values (term ((valid? CON_1) ... (valid? CON_2))))]
  [(valid? (CON_1 ... ->* CON_2))
   ,(andmap values (term ((valid? CON_1) ... (valid? CON_2))))])

;; A flat contract can be checked immediately.
(define-metafunction λc-user
  flat? : CON -> #t or #f
  [(flat? X) #t]
  [(flat? (atom/c ATOMLIT any)) #t]
  [(flat? (pred PREDV any)) #t]
  [(flat? (rec/c X CON)) (flat? CON)]
  [(flat? (cons/c CON_1 CON_2))
   ,(and (term (flat? CON_1))
         (term (flat? CON_2)))]
  [(flat? (struct/c X_1 X_2 CON ...))
   ,(andmap values (term ((flat? CON) ...)))]
  [(flat? (and/c CON_1 CON_2))
   ,(and (term (flat? CON_1))
         (term (flat? CON_2)))]  
  [(flat? (or/c CON_1 CON_2))
   ,(and (term (flat? CON_1))
         (term (flat? CON_2)))]
  [(flat? (not/c CON)) (flat? CON)]
  [(flat? CARROW) #f])

(define-metafunction λc-user
  subst/μ : X CON CON -> CON
  [(subst/μ X CON X) CON]
  [(subst/μ X CON X_0) X_0]
  [(subst/μ X CON (atom/c ATOMLIT any)) (atom/c ATOMLIT any)]
  [(subst/μ X CON (and/c CON_0 CON_1))
   (and/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]
  [(subst/μ X CON (or/c CON_0 CON_1))
   (or/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]
  [(subst/μ X CON (not/c CON_0))
   (not/c (subst/μ X CON CON_0))]
  [(subst/μ X CON (cons/c CON_0 CON_1))
   (cons/c (subst/μ X CON CON_0) (subst/μ X CON CON_1))]
  [(subst/μ X CON (struct/c X_1 X_2 CON_0 ...))
   (struct/c X_1 X_2 (subst/μ X CON CON_0) ...)]
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
 (redex-check λc-user (X PCON_1 PCON_2) (term (subst/μ X PCON_1 PCON_2))))


;; https://github.com/samth/var/issues/3
(test 
 (define CON? (redex-match λcρ CON))
 (define PCON? (redex-match λcρ PCON))
 (test-predicate (negate PCON?) (term (rec/c X (or/c (cons/c X X) (-> (pred string? †))))))           
 (test-predicate CON? (term (rec/c X (or/c (cons/c X X) (-> (pred string? †))))))            
 (test-predicate CON? (term X))
 (test-predicate (negate PCON?) (term X))
 
 (test-predicate 
  (negate (redex-match λcρ MOD))
  (term (module f racket
          (require)
          (define v (cons (λ () "a") (λ () "b"))) 
          (provide/contract 
           [v (rec/c X (or/c (cons/c X X) (-> (pred string? f))))])))))

(define (program-modules ls)
  (drop-right ls 2))
