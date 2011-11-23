#lang racket
(require "lang.rkt" "meta.rkt" "step.rkt" "garbage.rkt" "util.rkt")
(require redex/reduction-semantics)
(test-suite test cesk)
(provide CESK inj CESK-trace-it CESK-run unload)

(current-direct? #f)

(define-metafunction λCESK
  inj : EXP -> ς
  [(inj EXP)
   (ev (↓ EXP (env)) (sto) MT)])

(define-metafunction λCESK
  bind : σ K -> (a σ)
  [(bind σ K)
   (a σ_1)
   (where (a) (alloc σ (K)))
   (where σ_1 (extend-sto σ a (K)))])

(define-metafunction λCESK
  ev : D σ K -> ς
  [(ev A σ MT) (A σ)]
  [(ev BLAME σ K) (BLAME σ)]
  [(ev V σ K) (co K V σ)]
  [(ev REDEX σ K) (ap REDEX σ K)]  
  [(ev PREVAL σ K) (ev (-- PREVAL) σ K)]
  [(ev (clos • ρ) σ K) (ev (join-contracts) σ K)]
  [(ev (clos (@ EXP ... LAB) ρ) σ K)
   (ev (@ (↓ EXP ρ) ... LAB) σ K)]
  [(ev (clos (@* EXP ... LAB) ρ) σ K)
   (ev (@* (↓ EXP ρ) ... LAB) σ K)]  
  [(ev (clos (if EXP ...) ρ) σ K)
   (ev (if (↓ EXP ρ) ...) σ K)]
  [(ev (clos (let ((X EXP) ...) EXP_1) ρ) σ K)
   (ev (let ((X (↓ EXP ρ)) ...) (↓ EXP_1 ρ)) σ K)]
  [(ev (clos (begin EXP EXP_1) ρ) σ K)
   (ev (begin (↓ EXP ρ) (↓ EXP_1 ρ)) σ K)]
  [(ev (clos MODREF ρ) σ K)
   (ev MODREF σ K)]
  [(ev (@ D_1 D_2 ... LAB) σ K)
   (ev D_1 σ_1 (APP () (D_2 ...) LAB a))
   (where (a σ_1) (bind σ K))]
  [(ev (@* D_1 D_2 ... LAB) σ K)
   (ev D_1 σ_1 (APP* () (D_2 ...) LAB a))
   (where (a σ_1) (bind σ K))]  
  [(ev (if D_1 D_2 D_3) σ K)
   (ev D_1 σ_1 (IF D_2 D_3 a))
   (where (a σ_1) (bind σ K))]
  [(ev (let () D) σ K)
   (ev D σ K)]
  [(ev (let ((X D) (X_1 D_1) ...) D_n) σ K)
   (ev D σ_1 (LET () X ((X_1 D_1) ...) D_n a))
   (where (a σ_1) (bind σ K))]
  [(ev (CON ρ <= LAB_1 LAB_2 V LAB_3 D) σ K)   
   (ev D σ_1 (CHECK CON ρ LAB_1 LAB_2 V LAB_3 a))
   (where (a σ_1) (bind σ K))]
  [(ev (begin D D_1) σ K)
   (ev D σ_1 (BEGIN D_1 a))
   (where (a σ_1) (bind σ K))]
  [(ev (ANYCON ρ <= LAB_1 LAB_2 V LAB_3 D) σ K)
   (ev D σ K)])
  
(define (ap Ms)
  (define r
    (union-reduction-relations v c c~ a d (m Ms) (m~ Ms)))
  (reduction-relation 
   λCESK #:domain ς
   (--> (ap D_redex σ K) 
        (gc-state (ev D_contractum σ_1 K))
        (where (any_0 ... (any_name (D_contractum σ_1)) any_1 ...)
               ,(apply-reduction-relation/tag-with-names r (term (D_redex σ))))
        (computed-name (term any_name)))))

(define co
  (reduction-relation
   λCESK #:domain ς
   (--> (co (APP (V_1 ...) (D_1 D_2 ...) LAB a) V σ)    
        (gc-state (ev D_1 σ (APP (V_1 ... V) (D_2 ...) LAB a)))
        co-next-@)
   (--> (co (APP* (V_1 ...) (D_1 D_2 ...) LAB a) V σ)    
        (gc-state (ev D_1 σ (APP* (V_1 ... V) (D_2 ...) LAB a)))
        co-next-@*)
   (--> (co (APP (V_1 ...) () LAB a) V σ)
        (gc-state (ap (@ V_1 ... V LAB) σ K))
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-@)
   (--> (co (APP* (V_1 ...) () LAB a) V σ)
        (gc-state (ap (@* V_1 ... V LAB) σ K))
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-@*)
   (--> (co (IF D_1 D_2 a) V σ)     
        (gc-state (ap (if V D_1 D_2) σ K))
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-if)
   (--> (co (LET ((X_1 V_1) ...) X ((X_2 D_2) (X_3 D_3) ...) D_b a) V σ)
        (gc-state (ev D_2 σ (LET ((X_1 V_1) ... (X V)) X_2 ((X_3 D_3) ...) D_b a)))
        co-next-let)
   (--> (co (LET ((X_1 V_1) ...) X () D_b a) V σ)
        (gc-state (ap (let ((X_1 V_1) ... (X V)) D_b) σ K))
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-let)
   (--> (co (BEGIN D a) V σ)
        (gc-state (ev D σ K))
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-begin)
   (--> (co (CHECK CON ρ LAB_1 LAB_2 V_1 LAB_3 a) V σ)    
        (gc-state (ap (CON ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ K))
        (where (S_0 ... K S_1 ...)
               (sto-lookup σ a))
        co-done-check)))

(define-metafunction λCESK
  unload : ς -> (D σ)
  [(unload (A σ)) (gc (A σ))]
  [(unload (ap D σ K)) (gc ((stick D K σ) σ))]
  [(unload (co K V σ)) (gc ((stick V K σ) σ))])

(test
 (test-equal (term (unload ((-- (clos 0 (env))) (sto))))
             (term ((-- (clos 0 (env))) (sto))))
 (test-equal (term (unload (ap (clos 0 (env)) (sto) MT)))
             (term ((clos 0 (env)) (sto))))
 (test-equal (term (unload (co MT (-- (clos 0 (env))) (sto))))
             (term ((-- (clos 0 (env))) (sto)))))

(define-metafunction λCESK
  stick : D K σ -> D
  [(stick D MT σ) D]
  [(stick D (APP (V ...) (D_1 ...) LAB a) σ)
   (stick (@ V ... D D_1 ... LAB) K σ)
   (where (S_0 ... K S_1 ...)
          (sto-lookup σ a))]
  [(stick D (APP* (V ...) (D_1 ...) LAB a) σ)
   (stick (@* V ... D D_1 ... LAB) K σ)
   (where (S_0 ... K S_1 ...)
          (sto-lookup σ a))]
  [(stick D (IF D_1 D_2 a) σ)
   (stick (if D D_1 D_2) K σ)
   (where (S_0 ... K S_1 ...)
          (sto-lookup σ a))]
  [(stick D (LET ((X V) ...) X_1 ((X_2 D_2) ...) D_1 a) σ)
   (stick (let ((X V) ... (X_1 D) (X_2 D_2) ...) D_1) K σ)
   (where (S_0 ... K S_1 ...)
          (sto-lookup σ a))]  
  [(stick D (BEGIN D_1 a) σ)
   (stick (begin D D_1) K σ)
   (where (S_0 ... K S_1 ...)
          (sto-lookup σ a))]
  [(stick D (DEM CON a) σ)
   (stick (dem CON D) K σ)
   (where (S_0 ... K S_1 ...)
          (sto-lookup σ a))]
  [(stick D (CHECK CON ρ LAB_1 LAB_2 V LAB_3 a) σ)
   (stick (CON ρ <= LAB_1 LAB_2 V LAB_3 D) K σ)
   (where (S_0 ... K S_1 ...)
          (sto-lookup σ a))])

(test
 (define D (term (clos 0 (env))))
 (define D1 (term (clos 1 (env))))
 (define D2 (term (clos 2 (env))))
 (define V1 (term (-- (clos 1 (env)))))
 (define V2 (term (-- (clos 2 (env)))))
 
 (test-equal (term (stick ,D MT (sto)))
             D) 
 (test-equal (term (stick ,D (APP (,V1 ,V2) (,D1 ,D2) f (loc a)) (sto [(loc a) (MT)])))
             (term (@ ,V1 ,V2 ,D ,D1 ,D2 f)))
 (test-equal (term (stick ,D (APP* (,V1 ,V2) (,D1 ,D2) f (loc a)) (sto [(loc a) (MT)])))
             (term (@* ,V1 ,V2 ,D ,D1 ,D2 f))) 
 (test-equal (term (stick ,D (IF ,D1 ,D2 (loc a)) (sto [(loc a) (MT)])))
             (term (if ,D ,D1 ,D2)))
 (test-equal (term (stick ,D (LET ((x ,V1) (y ,V2)) z ((p ,D1)) ,D2 (loc a)) (sto [(loc a) (MT)])))
             (term (let ((x ,V1) (y ,V2) (z ,D) (p ,D1)) ,D2)))
 (test-equal (term (stick ,D (BEGIN ,D1 (loc a)) (sto [(loc a) (MT)])))
             (term (begin ,D ,D1)))
 (test-equal (term (stick ,D (DEM (∧) (loc a)) (sto [(loc a) (MT)])))
             (term (dem (∧) ,D)))
 (test-equal (term (stick ,D (CHECK (∧) (env) f g ,V1 h (loc a)) (sto [(loc a) (MT)])))
             (term ((∧) (env) <= f g ,V1 h ,D))))


(define (CESK Ms)
  (union-reduction-relations co (ap Ms)))

(define (CESK-run P)
  (apply-reduction-relation* (CESK (program-modules P))
                             (term (inj ,(last P)))))
                      
(define-syntax-rule (CESK-trace-it P . rest)
  (traces (CESK (program-modules P))
          (term (inj ,(last P)))
          ;; #:pred (colorize (program-modules P))
          . rest))