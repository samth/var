#lang racket
(require "lang.rkt" "check.rkt" "meta.rkt" "util.rkt")
(require redex/reduction-semantics)
(test-suite test simple-cesk)

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
  (S V K))



(define-metafunction λCESK
  restrict : EXP ρ -> ρ
  ;; FIXME : dummy placeholder for now.
  [(restrict EXP ρ) ρ])

(define-metafunction λCESK
  ↓ : EXP ρ -> D
  [(↓ EXP ρ) (clos EXP (restrict EXP ρ))])
  

(define-metafunction λCESK
  bind : σ K -> (a σ)
  [(bind σ K)
   (a σ_1)
   (where (a) (alloc σ (K)))
   (where σ_1 (extend-sto σ a (K)))])

(define (set->list s) (for/list ([x (in-set s)]) x))

(define-metafunction λCESK
  lookup : ρ X -> a
  [(lookup ρ X)
   (loc ,(hash-ref (term ρ) (term X)))])

(test-equal 
 (apply set
        (term (deref ,(hash 0 (set (term (-- (clos 1 (env))))
                                   (term (-- (clos 2 (env))))
                                   (term (-- (clos 3 (env))))))
                     (loc 0))))
 (set (term (-- (clos 1 (env))))
      (term (-- (clos 2 (env))))
      (term (-- (clos 3 (env))))))


(define ev
  (reduction-relation 
   λCESK #:domain ς     
   (--> (ev (clos VAL ρ) σ K) (co K (-- (↓ VAL ρ)) σ))
   (--> (ev (clos X ρ) σ K)
        (co K V σ)
        (where (any_1 ... V any_2 ...)
               (deref σ (lookup ρ X))))

   (--> (ev (clos MODREF ρ) σ K)
        (ap MODREF σ K))
   
   (--> (ev (clos (@ EXP EXP_1 ... LAB) ρ) σ K)
        (ev (↓ EXP ρ) σ_1 (APP () ((↓ EXP_1 ρ) ...) LAB a))
        (where (a σ_1) (bind σ K)))
   
   (--> (ev (clos (if EXP_1 EXP_2 EXP_3) ρ) σ K)
        (ev (↓ EXP_1 ρ) σ_1 (IF (↓ EXP_2 ρ) (↓ EXP_3 ρ) a))
        (where (a σ_1) (bind σ K)))

   (--> (ev (clos (let () EXP) ρ) σ K)
        (ev (↓ EXP ρ) σ K))
   (--> (ev (clos (let ((X_1 EXP_1) (X_2 EXP_2) ...) EXP_3) ρ) σ K)
        (ev (↓ EXP_1 ρ) σ_1 (LET () X_1 ((X_2 (↓ EXP_2 ρ)) ...) (↓ EXP_3 ρ) a))
        (where (a σ_1) (bind σ K)))
   
   (--> (ev (clos (begin EXP_1 EXP_2) ρ) σ K)
        (ev (↓ EXP_1 ρ) σ_1 (BEGIN (↓ EXP_2 ρ) a))
        (where (a σ_1) (bind σ K)))))

(test
 (test--> ev
          (term (ev (clos 0 (env)) (sto) MT))
          (term (co MT (-- (↓ 0 (env))) (sto))))
 (test--> ev
          (term (ev (clos x (env (x 0)))
                    (sto (0 ((-- (clos 4 (env))))))
                    MT))
          (term (co MT (-- (clos 4 (env))) (sto (0 ((-- (clos 4 (env)))))))))
 (test--> ev
          (term (ev (clos (x ^ f g) (env)) (sto) MT))
          (term (ap (x ^ f g) (sto) MT)))
 (test--> ev
          (term (ev (clos (@ f x †) (env)) (sto) MT))
          (redex-let λCESK (((a σ) (term (bind (sto) MT))))
                     (term (ev (↓ f (env)) σ (APP () ((↓ x (env))) † a)))))
 (test--> ev
          (term (ev (clos (if 0 1 2) (env)) (sto) MT))
          (redex-let λCESK (((a σ) (term (bind (sto) MT))))
                     (term (ev (↓ 0 (env)) σ (IF (↓ 1 (env)) (↓ 2 (env)) a))))) 
 (test--> ev
          (term (ev (clos (let () x) (env)) (sto) MT))
          (term (ev (clos x (env)) (sto) MT)))
 (test--> ev
          (term (ev (clos (let ((x 1) (y 2)) 3) (env)) (sto) MT))
          (redex-let λCESK (((a σ) (term (bind (sto) MT))))
                     (term (ev (↓ 1 (env)) σ (LET () x ((y (↓ 2 (env)))) (↓ 3 (env)) a)))))
          
 (test--> ev
          (term (ev (clos (begin x y) (env)) (sto) MT))
          (redex-let λCESK (((a σ) (term (bind (sto) MT))))
                     (term (ev (↓ x (env)) σ (BEGIN (↓ y (env)) a))))))

(require "step-c.rkt")
(define ap-c
  (reduction-relation 
   λCESK #:domain ς
   (--> (ap D_redex σ K) 
        (ev D_contractum σ K)
        (where (any_0 ... D_contractum any_1 ...)
               ,(apply-reduction-relation c (term D_redex))))))

        
(define co
  (reduction-relation
   λCESK #:domain ς
   (--> (co (APP (V_1 ...) ((clos EXP ρ) D ...) LAB a) V σ)    
        (ev EXP ρ σ (APP (V_1 ... V) (D ...) LAB a)))
   (--> (co (APP (V_1 ...) () LAB a) V σ)    
        (ap (@ V_1 ... V LAB) σ K)
        (where (S_0 ... K S_1 ...)
               (deref σ a)))
   (--> (co (IF D_1 D_2 a) V σ)     
        (ap (if V D_1 D_2) σ K)
        (where (S_0 ... K S_1 ...)
               (deref σ a)))
   (--> (co (LET ((X_1 V_1) ...) X ((X_2 (clos EXP ρ)) (X_3 D) ...) D_b a) V σ)
        (ev EXP ρ σ (LET ((X_1 V_1) ... (X V)) X_2 ((X_3 D) ...) D_b a)))
   (--> (co (LET ((X_1 V_1) ...) X () D_b a) V σ)
        (ap (let ((X_1 V_1) ... (X V)) D_b) σ K)
        (where (S_0 ... K S_1 ...)
               (deref σ a)))
   (--> (co (BEGIN (clos EXP ρ) a) V σ)
        (ev EXP ρ σ K)
        (where (S_0 ... K S_1 ...)
               (deref σ a)))
   (--> (co (CHECK CON ρ LAB_1 LAB_2 V_1 LAB_3 a) V σ)    
        (ap (CON ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ K)
        (where (S_0 ... K S_1 ...)
               (deref σ a)))))
    
                      

                      
  
     
     
     
     
     
     