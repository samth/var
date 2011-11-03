#lang racket
(require "lang.rkt" "meta.rkt" "util.rkt")
(require redex/reduction-semantics)
(test-suite test simple-cesk)
(provide CESK inj)

(define-extended-language λCESK λcρ
  ; Continuations
  (K MT
     (APP (V ...) (D ...) LAB a)           ; (@ V ... 𝓔 D ... LAB)
     (IF D D a)                            ; (if 𝓔 D D) 
     (LET ((X V) ...) X ((X D) ...) D a)   ; (let ((X V) ... (X 𝓔) (X D) ...) D)
     (BEGIN D a)                           ; (begin 𝓔 D)
     (CHECK CON ρ LAB LAB V LAB a))        ; (CON ρ <= LAB LAB V LAB 𝓔)

  ; States
  (ς (ev D σ K)
     (ap D σ K)
     (co K V σ))
  
  ; Potential redexes (that do real work).
  (REDEX (clos • ρ)
         (clos X ρ)
         (V V ...)
         (if V D D)
         (begin V D)
         (let ((X V) ...) D)      
         MODREF   
         (CON ρ <= LAB LAB V LAB V)
         BLAME)
  
  (S K V))

(define-metafunction λCESK
  inj : EXP -> ς
  [(inj EXP)
   (ev (clos EXP (env)) (sto) MT)])

(define-metafunction λCESK
  bind : σ K -> (a σ)
  [(bind σ K)
   (a σ_1)
   (where (a) (alloc σ (K)))
   (where σ_1 (extend-sto σ a (K)))])

(define-metafunction λCESK
  ev : D σ K -> ς
  [(ev V σ K) (co K V σ)]
  [(ev REDEX σ K) (ap REDEX σ K)]
  [(ev PREVAL σ K) (ev (-- PREVAL) σ K)]
  [(ev (clos (@ EXP ... LAB) ρ) σ K)
   (ev (@ (clos EXP ρ) ... LAB) σ K)]
  [(ev (clos (if EXP ...) ρ) σ K)
   (ev (if (clos EXP ρ) ...) σ K)]
  [(ev (clos (let ((X EXP) ...) EXP_1) ρ) σ K)
   (ev (let ((X (clos EXP ρ)) ...) (clos EXP_1 ρ)) σ K)]
  [(ev (clos (begin EXP EXP_1) ρ) σ K)
   (ev (begin (clos EXP ρ) (clos EXP_1 ρ)) σ K)]
  [(ev (clos MODREF ρ) σ K)
   (ev MODREF σ K)]
  [(ev (@ D_1 D_2 ... LAB) σ K)
   (ev D_1 σ_1 (APP () (D_2 ...) LAB a))
   (where (a σ_1) (bind σ K))]
  [(ev (if D_1 D_2 D_3) σ K)
   (ev D_1 σ_1 (IF D_2 D_3 a))
   (where (a σ_1) (bind σ K))]
  [(ev (let () D) σ K)
   (ev D σ K)]
  [(ev (let ((X D) (X_1 D_1) ...) D_n) σ K)
   (ev D σ_1 (LET () X ((X_1 D_1) ...) D_n a))
   (where (a σ_1) (bind σ K))]
  [(ev (begin D D_1) σ K)
   (ev D σ_1 (BEGIN D_1 a))
   (where (a σ_1) (bind σ K))])
  
(require "step.rkt")
(define (ap Ms)
  (define r
    (union-reduction-relations v c c~ (m Ms) (m~ Ms)))
  (reduction-relation 
   λCESK #:domain ς
   (--> (ap D_redex σ K) 
        (ev D_contractum σ_1 K)
        (where (any_0 ... (any_name (D_contractum σ_1)) any_1 ...)
               ,(apply-reduction-relation/tag-with-names r (term (D_redex σ))))
        (computed-name (term any_name)))))

(define co
  (reduction-relation
   λCESK #:domain ς
   (--> (co (APP (V_1 ...) ((clos EXP ρ) D ...) LAB a) V σ)    
        (ev (clos EXP ρ) σ (APP (V_1 ... V) (D ...) LAB a))
        co-next-@)            
   (--> (co (APP (V_1 ...) () LAB a) V σ)
        (ap (@ V_1 ... V LAB) σ K)
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-@)
   (--> (co (IF D_1 D_2 a) V σ)     
        (ap (if V D_1 D_2) σ K)
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-if)
   (--> (co (LET ((X_1 V_1) ...) X ((X_2 (clos EXP ρ)) (X_3 D) ...) D_b a) V σ)
        (ev (clos EXP ρ) σ (LET ((X_1 V_1) ... (X V)) X_2 ((X_3 D) ...) D_b a))
        co-next-let)
   (--> (co (LET ((X_1 V_1) ...) X () D_b a) V σ)
        (ap (let ((X_1 V_1) ... (X V)) D_b) σ K)
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-let)
   (--> (co (BEGIN D a) V σ)
        (ev D σ K)
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-begin)
   (--> (co (CHECK CON ρ LAB_1 LAB_2 V_1 LAB_3 a) V σ)    
        (ap (CON ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ K)
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-check)))

(define (CESK Ms)
  (union-reduction-relations co (ap Ms)))
                      