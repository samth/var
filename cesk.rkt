#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "name.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test cek)

(define-extended-language CESK* λc~ 
  (K mt 
     
     (ap clo ... E ... ρ ℓ a)
     
     (if E E ρ a)
     (op o clo ... E ... ρ ℓ a)
     (let x E ρ a)
     (beg E ρ a)
     (chk C ℓ ℓ V ℓ a))  ;; V?
  
  (a any)
  (ρ ((x a) ...))
  (clo (V ρ))
  (D clo K)
  (σ ((a {D}) ...))
  (ς (E ρ σ K)))

(define-metafunction CESK*
  alloc : σ (any ..._1) -> (a ..._1)
  [(alloc σ (any ...)) 
   ,(variables-not-in (term σ) (term (any ...)))])

(define-metafunction CESK*
  extend-env : ρ (x ..._1) (a ..._1) -> ρ
  [(extend-env ((x_0 a_0) ...) (x ..._1) (a ..._1))
   ((x a) ... (a_0 a_0) ...)])

(define-metafunction CESK*
  extend-sto : σ (a ..._1) (D ..._1) -> σ
  [(extend-sto ((a_0 {D_0 ...}) ...) (a ..._1) (D ..._1))
   ((a {D}) ... (a_0 {D_0 ...}) ...)])

(define-metafunction CESK*
  sto-lookup : σ a -> {D ...}
  [(sto-lookup ((a_0 {D_0 ...}) ... (a {D ...}) (a_1 {D_1 ...}) ...) a) {D ...}])

(define-metafunction CESK*
  env-lookup : ρ x -> a
  [(env-lookup ((x a) (x_0 a_0) ...) x) a]
  [(env-lookup ((x_0 a_0) (x_1 a_1) ...) x)
   (env-lookup ((x_1 a_1) ...) x)])

(define-metafunction CESK*
  load : E -> ς
  [(load E)
   (E () () mt)])

(define step
  (reduction-relation
   CESK* #:domain ς

   ;; Reductions
   
   (--> (x ρ σ K)
        (V ρ_0 σ K)
        (where (D_0 ... (V ρ_0) D_1 ...)
               (sto-lookup σ (env-lookup ρ x))))
   
   (--> (PV ρ σ K) ((-- PV) ρ σ K) wrap)
   
   (--> (V ρ σ (ap ((-- (λ (x ...) E) C ...) ρ_0) clo ... ρ_1 ℓ a))
        (E (extend-env ρ (x ...) (a_1 ...))
           (extend-sto σ (a_1 ...) (clo ... (V ρ)))
           K)
        (where (a_1 ...) (alloc σ (x ...)))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        (side-condition (= (length (term (x ...)))
                           (add1 (length (term (clo ...))))))
        β)
   
   (--> (V ρ σ (ap ((-- (λ x_f (x ...) E) C ...) ρ_0) clo ... ρ_1 ℓ a))
        (E (extend-env ρ (x_f x ...) (a_1 ...))
           (extend-sto σ (a_1 ...) (((-- (λ x_f (x ...) E) C ...) ρ_0) clo ... (V ρ)))
           K)
        (where (a_1 ...) (alloc σ (x_f x ...)))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))    
        (side-condition (= (length (term (x ...)))
                           (add1 (length (term (clo ...))))))
        β-rec)      
   
   (--> (U ρ σ (ap ((V ρ_0) clo ... ρ_1 ℓ a)))
        ((blame ℓ  Λ V λ V) ρ_0 σ K)
        (side-condition (term (∈ #t (δ (@ proc? V ★)))))
        (side-condition (not (equal? (add1 (length (term (clo ...))))
                                     (term (arity V)))))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        blame-arity)
   
   (--> (U ρ σ (ap ((V ρ_0) clo ... ρ_1 ℓ a)))
        ((blame ℓ  Λ V λ V) ρ_0 σ K)
        (side-condition (term (∈ #f (δ (@ proc? V ★)))))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        blame-not-proc)  
   
   (--> (V ρ σ (if E_1 E_2 ρ_1 a))
        (E_1 ρ_1 σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        (side-condition (term (∈ #f (δ (@ false? V ★)))))
        if-t)
   
   (--> (V ρ σ (if E_1 E_2 ρ_2 a))
        (E_2 ρ_2 σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        (side-condition (term (∈ #t (δ (@ false? V ★)))))
        if-f)   
   
   (--> (V ρ σ (op o (V_0 ρ_0) ... ρ_1 ℓ a))
        (V-or-B () σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))         
        (where (V-or-B_1 ... V-or-B V-or-B_2 ...)
               (δ (@ o V_0 ... V ℓ)))
        δ)
   
   (--> (V ρ σ (beg E ρ_0 a))
        (E ρ_0 σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        begin)
        
   (--> (V ρ σ (let x E ρ_0 a))
        (E (extend-env ρ_0 (x) (a_0))
           (extend-sto σ (a_0) ((V ρ)))
           K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        (where (a_0) (alloc σ (x)))
        let)  

   ;; Context shuffling
   
   (--> (V ρ σ (ap clo ... E_0 E ... ρ_0 ℓ a))
        (E_0 ρ_0 σ (ap clo ... (V ρ) E ... ρ_0 ℓ a))
        ap-next)
   
   (--> ((@ E_0 E_1 ... ℓ) ρ σ K)
        (E_0 ρ σ_0 (ap E_1 ... ρ ℓ a))       
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto σ (a) (K)))
        ap-push)
   
   (--> ((if E_0 E_1 E_2) ρ σ K)
        (E_0 ρ σ_0 (if E_1 E_2 ρ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto σ (a) (K)))
        if-push)
   
   (--> (V ρ σ (op o clo ... E_0 E ... ρ_0 ℓ a))
        (E_0 ρ_0 σ (op o clo ... (V ρ) E ... ρ_0 ℓ a))
        op-next)
   
   (--> ((@ o E_0 E_1 ... ℓ) ρ σ K)
        (E_0 ρ σ_0 (op o E_1 ... ρ ℓ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto σ (a) (K)))
        op-push)
   
   (--> ((begin E_0 E_1) ρ σ K)
        (E_0 ρ σ_0 (beg E_1 ρ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto σ (a) (K)))
        beg-push)
   
   (--> ((let x E_0 E_1) ρ σ K)
        (E_0 ρ σ_0 (let x E_1 ρ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto σ (a) (K)))
        let-push)))


(require redex)
(require "annotate.rkt")
(define (f e)
  (traces step
          (term (load (ann-exp ,e † ())))))




