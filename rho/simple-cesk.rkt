#lang racket
(require "lang.rkt" "check.rkt" "util.rkt")
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
  (ς (ev EXP ρ σ K)
     (ap D σ K)
     (co K V σ))
  
  (σ (side-condition any hash?))
  (ρ (side-condition any hash?))
  
  (S V K)
  (a (loc any)))

(define-metafunction λCESK
  mt-ρ : -> ρ
  [(mt-ρ) #hash()])
(define-metafunction λCESK
  mt-σ : -> σ
  [(mt-σ) #hash()])

(define-metafunction λCESK
  restrict : EXP ρ -> ρ
  ;; FIXME : dummy placeholder for now.
  [(restrict EXP ρ) ρ])

(define-metafunction λCESK
  ↓ : EXP ρ -> D
  [(↓ EXP ρ) (clos EXP (restrict EXP ρ))])

(define-metafunction λCESK
  alloc-addr : σ (any ..._1) -> (any ..._1)
  [(alloc-addr σ (any ...))
   ,(variables-not-in* (term σ) (term (any ...)))
   (side-condition (current-exact?))]
  [(alloc-addr σ (X ...))
   (X ...) #;
   ,(variables-not-in (term σ) (term (X ...)))]
  [(alloc-addr σ (K ...))
   ,(map (λ (p) (if (and (pair? p)) (car p) p)) (term (K ...)))]
  [(alloc-addr σ (V ...))
   ,(build-list (length (term (V ...))) values)])

(define-metafunction λCESK
  alloc : σ (any ..._1) -> (a ..._1)
  [(alloc σ (any ...))
   ((loc any_1) ...)
   (where (any_1 ...) (alloc-addr σ (any ...)))])

(define-metafunction λCESK
  extend-env : ρ X a -> ρ
  [(extend-env ρ X (loc any_a))
   ,(hash-set (term ρ) (term X) (term any_a))])

(test 
 (test-equal (term (extend-env (mt-ρ) x (loc 0)))
             (hash 'x 0)))

(define-metafunction λCESK
  extend-sto : σ a (any ...) -> σ
  [(extend-sto σ (loc any_a) (any ...))
   ,(hash-set (term σ) (term any_a)
              (set-union (apply set (term (any ...)))
                         (hash-ref (term σ) (term any_a) (set))))])

(test
 (test-equal (term (extend-sto ,(hash) (loc 0) (x y z)))
             (hash 0 (set 'x 'y 'z)))
 (test-equal (term (extend-sto ,(hash 0 (set 'x 'y 'z)) (loc 0) (q)))
             (hash 0 (set 'x 'y 'z 'q))))
             
  

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

(define-metafunction λCESK
  deref : σ a -> (S ...)
  [(deref σ (loc any_a))
   ,(set->list (hash-ref (term σ) (term any_a)))])

(test-equal 
 (apply set
        (term (deref ,(hash 0 (set (term (-- (clos 1 ())))
                                   (term (-- (clos 2 ())))
                                   (term (-- (clos 3 ())))))
                     (loc 0))))
 (set (term (-- (clos 1 ())))
      (term (-- (clos 2 ())))
      (term (-- (clos 3 ())))))


(define ev
  (reduction-relation 
   λCESK #:domain ς     
   (--> (ev VAL ρ σ K) (co K (-- (↓ VAL ρ)) σ))
   (--> (ev X ρ σ K)
        (co K V σ)
        (where (any_1 ... V any_2 ...)
               (deref σ (lookup ρ X))))

   (--> (ev MODREF ρ σ K)
        (ap MODREF σ K))
   
   (--> (ev (@ EXP EXP_1 ... LAB) ρ σ K)
        (ev EXP ρ σ_1 (APP () ((↓ EXP_1 ρ) ...) LAB a))
        (where (a σ_1) (bind σ K)))
   
   (--> (ev (if EXP_1 EXP_2 EXP_3) ρ σ K)
        (ev EXP_1 ρ σ_1 (IF (↓ EXP_2 ρ) (↓ EXP_3 ρ) a))
        (where (a σ_1) (bind σ K)))

   (--> (ev (let () EXP) ρ σ K)
        (ev EXP ρ σ K))
   (--> (ev (let ((X_1 EXP_1) (X_2 EXP_2) ...) EXP_3) ρ σ K)
        (ev EXP_1 ρ σ_1 (LET () X_1 ((X_2 (↓ EXP_2 ρ)) ...) (↓ EXP_3 ρ) a))
        (where (a σ_1) (bind σ K)))
   
   (--> (ev (begin EXP_1 EXP_2) ρ σ K)
        (ev EXP_1 ρ σ_1 (BEGIN (↓ EXP_2 ρ) a))
        (where (a σ_1) (bind σ K)))))

(test
 (test--> ev
          (term (ev 0 (mt-ρ) (mt-σ) MT))
          (term (co MT (-- (↓ 0 (mt-ρ))) (mt-σ))))
 (test--> ev
          (term (ev x 
                    (extend-env (mt-ρ) x (loc 0))
                    (extend-sto (mt-σ) (loc 0) ((-- (clos 4 ()))))
                    MT))
          (term (co MT (-- (clos 4 ())) (extend-sto (mt-σ) (loc 0) ((-- (clos 4 ())))))))
 (test--> ev
          (term (ev (x ^ f g) (mt-ρ) (mt-σ) MT))
          (term (ap (x ^ f g) (mt-σ) MT))) 
 (test--> ev
          (term (ev (@ f x †) (mt-ρ) (mt-σ) MT))
          (redex-let λCESK (((a σ) (term (bind (mt-σ) MT))))
                     (term (ev f (mt-ρ) σ (APP () ((↓ x (mt-ρ))) † a))))) 
 (test--> ev
          (term (ev (if 0 1 2) (mt-ρ) (mt-σ) MT))
          (redex-let λCESK (((a σ) (term (bind (mt-σ) MT))))
                     (term (ev 0 (mt-ρ) σ (IF (↓ 1 (mt-ρ)) (↓ 2 (mt-ρ)) a))))) 
 (test--> ev
          (term (ev (let () x) (mt-ρ) (mt-σ) MT))
          (term (ev x (mt-ρ) (mt-σ) MT)))
 (test--> ev
          (term (ev (let ((x 1) (y 2)) 3) (mt-ρ) (mt-σ) MT))
          (redex-let λCESK (((a σ) (term (bind (mt-σ) MT))))
                     (term (ev 1 (mt-ρ) σ (LET () x ((y (↓ 2 (mt-ρ)))) (↓ 3 (mt-ρ)) a)))))
          
 (test--> ev
          (term (ev (begin x y) (mt-ρ) (mt-σ) MT))
          (redex-let λCESK (((a σ) (term (bind (mt-σ) MT))))
                     (term (ev x (mt-ρ) σ (BEGIN (↓ y (mt-ρ)) a))))))

(define ap
  (reduction-relation 
   λCESK #:domain ς
   (--> (ap (FLAT ρ <= LAB_1 LAB_2 V_1 LAB_3 V) σ K)        
        (ap (@ (flat-check (FLAT ρ) V) V Λ) 
            σ_1
            (IF (remember-contract V (FLAT ρ))
                (blame LAB_1 LAB_3 V_1 (FLAT ρ) V)
                a))
        (where (a σ_1) (bind σ K))
        flat-check)))

(apply-reduction-relation ap
                          (term (ap ((pred string? †) (mt-ρ) <= f g (-- (clos "x" (mt-ρ))) f (-- (clos "x" (mt-ρ))))
                                    (mt-σ)
                                    MT)))
        
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
    
                      

                      
  
     
     
     
     
     
     