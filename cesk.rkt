#lang racket
(require (except-in redex plug))
(require "lang.rkt" "meta.rkt" "name.rkt" "util.rkt" "annotate.rkt" "examples.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test cesk)

(current-cache-all? #t)

(define-extended-language CESK* λc~ 
  (K mt      
     (ap clo ... E ... ρ ℓ a)     
     (if E E ρ a)
     (op o clo ... E ... ρ ℓ a)
     (let x E ρ a)
     (beg E ρ a)
     (chk C ℓ ℓ V-or-AE ℓ a)  ;; V?
     (dem AV a))
   
  (ρ ((x a) ...))
  (clo (V ρ))
  (D clo K)
  (σ ((a {D ...}) ...))
  (ς (E ρ σ K)))

(define-metafunction CESK*
  widen : V-or-B -> V-or-B
  [(widen B) B]
  [(widen AV) AV]
  [(widen (-- bool C ...)) (-- bool C ...)]
  [(widen (-- nat C ...)) (remember-contract (-- (nat/c)) C ...)]
  [(widen (-- string C ...)) (remember-contract (-- (string/c)) C ...)]
  [(widen (-- (cons V_1 V_2) C ...)) 
   (remember-contract (-- (pred cons? Λ)) C ...)]
  [(widen (-- empty C ...)) (-- empty C ...)]
  [(widen (-- L C ...)) (-- L C ...)]
  [(widen (-- PV C ...)) (remember-contract (-- (any/c)) C ...)])

;; handles the second arg not being symbols
(define (variables-not-in* a bs)
  (variables-not-in a (map (λ (b) (if (symbol? b) b 'loc)) bs)))

(define-metafunction CESK*
  alloc : σ (any ..._1) -> (a ..._1)
  [(alloc σ (x ...))
   (x ...)]
  [(alloc σ (K ...))
   ,(map (λ (p) (if (pair? p) (all-but-last p) p)) (term (K ...)))]
  [(alloc σ (V ...))
   ,(build-list (length (term (V ...))) values)]
  #;#;
  [(alloc σ (K ...)) ,(build-list (length (term (K ...))) values)]
  [(alloc σ (any ...)) 
   ,(variables-not-in* (term σ) (term (any ...)))])

(define-metafunction CESK*
  extend-env : ρ (x ..._1) (a ..._1) -> ρ
  [(extend-env ((x_0 a_0) ...) (x ..._1) (a ..._1))
   ((x a) ... (a_0 a_0) ...)])

(define-metafunction CESK*
  extend-set : (any ...) (any ...) ->  (any ...)
  [(extend-set (any_1 ...) (any_2 ...))
   ,(sort (remove-duplicates (term (any_1 ... any_2 ...)))
          < #:key equal-hash-code)])

(define-metafunction CESK*
  extend-sto1 : σ a D -> σ
  [(extend-sto1 ((a_0 {D_0 ...}) ... (a {D_2 ...}) (a_1 {D_1 ...}) ...) a D)
   ((a_0 {D_0 ...}) ... (a (extend-set {D} {D_2 ...}))  (a_1 {D_1 ...}) ...)]
  [(extend-sto1 ((a_0 {D_0 ...}) ...) a D)
   ((a_0 {D_0 ...}) ... (a {D}))])

(define (addr< a b)
  (< (equal-hash-code a) (equal-hash-code a)))

(define-metafunction CESK*
  extend-sto : σ (a ..._1) (D ..._1) -> σ
  [(extend-sto σ () ()) ,(sort (term σ) addr< #:key car)]
  [(extend-sto σ (a a_1 ...) (D D_1 ...))
   (extend-sto (extend-sto1 σ a D) (a_1 ...) (D_1 ...))])

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

;; this will stop working once there's real non-determinism
(define-metafunction CESK*
  plug : E K -> E
  [(plug E mt) E]
  [(plug E (if E_1 E_2 ρ a)) (if E E_1 E_2)]
  [(plug E (op o (V ρ_1) ... E_1 ... ρ ℓ a))
   (@ o V ... E E_1 ... ℓ)]
  [(plug E (ap (V ρ_1) ... E_1 ... ρ ℓ a))
   (@ V ... E E_1 ... ℓ)]
  [(plug E (let x E_1 ρ a))
   (let x E E_1)]
  [(plug E (beg E_1 ρ a))
   (begin E E_1)]
  [(plug E (chk C ℓ_1 ℓ_2 V ℓ_3 a))
   (C <= ℓ_1 ℓ_2 V ℓ_3 E)])

(define-metafunction CESK*
  addr-of : K -> a
  ;; the address always goes last!
  [(addr-of (any ... a)) a])

(define-metafunction CESK*
  unload : ς -> E
  [(unload (E ρ σ mt))
   E]
  [(unload (E ρ σ K))
   (unload ((plug E K) ρ σ K_1))
   (where {D_0 ... K_1 D_1 ...} (sto-lookup σ (addr-of K)))])

(define step
  (reduction-relation
   CESK* #:domain ς
   
   ;; Reductions
   
   (--> (x ρ σ K)
        (V ρ_0 σ K)
        (where (D_0 ... (V ρ_0) D_1 ...)
               (sto-lookup σ (env-lookup ρ x)))
        var)
   
   (--> ((addr a) ρ σ K)
        (V ρ_0 σ K)
        (where (D_0 ... (V ρ_0) D_1 ...)
               (sto-lookup σ a))
        addr)
   
   (--> (PV ρ σ K) ((-- PV) ρ σ K) wrap)
  
   ;; Nullary function application
   (--> ((-- (λ () E) C ...) ρ σ (ap ρ_1 ℓ a))
        (E ρ σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        β-0)
   (--> ((-- (λ x () E) C ...) ρ σ (ap ρ_1 ℓ a))
        (E (extend-env ρ (x) (a_1))
           (extend-sto1 σ a_1 ((-- (λ x () E) C ...) ρ))
           K)
        (where (a_1) (alloc σ (x)))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        β-rec0)   
   
   ;; Unary+ function application
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
   
   (--> (U ρ σ (ap (V ρ_0) clo ... ρ_1 ℓ a))
        ((blame ℓ  Λ V λ V) ρ_0 σ K)
        (side-condition (term (∈ #t (δ (@ proc? V ★)))))
        (side-condition (not (equal? (add1 (length (term (clo ...))))
                                     (term (arity V)))))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        blame-arity)
   
   (--> (U ρ σ (ap (V ρ_0) clo ... ρ_1 ℓ a))
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
        ((widen V-or-B) () σ K)
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
   
   
   ;; Contract checking
   
   (--> (V ρ σ (chk FLAT ℓ_1 ℓ_2 V-or-AE ℓ_3 a))        
        ((flat-check (FLAT <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)) ρ σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        flat-check)
   
   (--> (V ρ σ (chk (or/c FLAT HOC) ℓ_1 ℓ_2 V-or-AE ℓ_3 a))        
        ((flat-check/defun FLAT V (remember-contract V FLAT) (HOC <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V)) ρ σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        check-or-pass)
   
   (--> (V ρ σ (chk (and/c C_0 C_1) ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        ((C_1 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 
              (C_0 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V))
         ρ σ K)
        (where HOC (and/c C_0 C_1))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        check-and-pass)
   
   (--> ((-- (cons V_0 V_1) C ...) ρ σ (chk (cons/c C_0 C_1) ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        ((@ cons 
            (C_0 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V_0)
            (C_1 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 V_1)
            Λ)
         ρ σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        (where HOC (cons/c C_0 C_1))
        check-cons-pass)
   
   (--> (V ρ σ (chk (C_1 ... -> C_2) ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        ((-- (λ (x ...)
               (C_2 <= ℓ_1 ℓ_2 V-or-AE ℓ_3 
                    (@ (addr a_new)
                       (C_1 <= ℓ_2 ℓ_1 x ℓ_3 x)
                       ...
                       Λ))))
         ρ σ_1 K)
        (where (x ...) ,(variables-not-in (term (C_1 ... C_2 V-or-AE))
                                          (map (λ _ 'x) (term (C_1 ...)))))
        #;
        (fresh ((x ...) (C_1 ...)))
        (where a_new (alloc σ (V)))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        (where σ_1 (extend-sto1 σ a_new (V ρ)))
        (side-condition (term (∈ #t (δ (@ proc? V ★)))))
        chk-fun-pass)
   
   (--> (V ρ σ (chk (C_1 ... -> C_2) ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        ((blame ℓ_1 ℓ_3 V-or-AE (C_1 ... -> C_2) V) ρ σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        (side-condition (term (∈ #f (δ (@ proc? V ★)))))
        chk-fun-fail-flat)
   
   ;; Nullary abstract application
   (--> (AV ρ_0 σ (ap ρ_1 ℓ a))
        ((remember-contract (-- (any/c)) C_0 ...) () σ K)
        (side-condition (term (∈ #t (δ (@ proc? AV ★)))))
        (side-condition (equal? 0 (term (arity AV))))        
        (where (-- C ...) AV)
        (where (C_0 ...) (range-contracts (C ...) ()))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        apply-abs0)
   
   ;; applying abstract values   
   (--> (V ρ σ (ap (AV ρ_1) clo ... ρ_0 ℓ a))
        ((demonic* C_demon U) ρ_2 σ (dem (remember-contract (-- (any/c)) C_0 ...) a))
        (where (clo_0 ..._1 (U ρ_2) clo_1 ..._2) ((V ρ) clo ...))
        (side-condition (term (∈ #t (δ (@ proc? AV ★)))))
        (side-condition (equal? (length (term (clo ... V)))
                                (term (arity AV))))
        (where (-- C ...) AV)
        (where ((C_D ...) ...) (domain-contracts (C ...)))
        (where (C_demon0 ..._1 C_demon C_demon1 ..._2) ((∧ C_D ...) ...))
        (where ((V_0 any_0) ...) (clo ... (V ρ)))              ;; FIXME, stripping environments because we're
        (where (C_0 ...) (range-contracts (C ...) (V_0 ...)))  ;; fucked here.
        
        apply-abs-known-arity)
   
   (--> (V ρ σ (ap (AV ρ_1) clo ... ρ_0 ℓ a))
        ((demonic* (any/c) U) ρ_2 σ (dem (-- (any/c)) a))
        (where (clo_0 ... (U ρ_2) clo_1 ...) ((V ρ) clo ...))
        (side-condition (term (∈ #t (δ (@ proc? AV ★)))))
        (side-condition ;; this is a proc with no arity, so it could be anything
         (not (term (arity AV))))
        apply-abs-no-arity)
   
   ;; SPLITTING OR/C and REC/C ABSTRACT VALUES
   ;; Some introduced values are infeasible, which is still sound.
   (--> ((-- C_0 ... (or/c C_1 ... C_2 C_3 ...) C ...) ρ σ K)
        ((remember-contract (-- (any/c) C_0 ... C ...) C_2)  ρ σ K)
        (side-condition (term (valid? C_2)))
        abs-or/c-split)
   
   (--> ((-- C_0 ... (rec/c x C_1) C ...) ρ σ K)
        ((remember-contract (-- (any/c) C_0 ... C ...)  (unroll (rec/c x C_1)))  ρ σ K)
        (side-condition (term (valid? (rec/c x C_1))))
        abs-rec/c-unroll)
   
   ;; Demonic
   
   (--> (V ρ σ (dem AV a))
        (AV () σ K)
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        dem-done)
   
   (--> (V ρ σ (dem (E_1 ρ_1) (E_2 ρ_2) ... AV a))
        (E_1 ρ_1 σ (dem (E_2 ρ_2) ... AV a))
        dem-continue)   
   
   ;; Context shuffling
   
   (--> (V ρ σ (ap clo ... E_0 E ... ρ_0 ℓ a))
        (E_0 ρ_0 σ (ap clo ... (V ρ) E ... ρ_0 ℓ a))
        ap-next)
   
   (--> ((@ E_0 E_1 ... ℓ) ρ σ K)
        (E_0 ρ σ_0 (ap E_1 ... ρ ℓ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto1 σ a K))
        ap-push)
   
   (--> ((if E_0 E_1 E_2) ρ σ K)
        (E_0 ρ σ_0 (if E_1 E_2 ρ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto1 σ a K))
        if-push)
   
   (--> (V ρ σ (op o clo ... E_0 E ... ρ_0 ℓ a))
        (E_0 ρ_0 σ (op o clo ... (V ρ) E ... ρ_0 ℓ a))
        op-next)
   
   (--> ((@ o E_0 E_1 ... ℓ) ρ σ K)
        (E_0 ρ σ_0 (op o E_1 ... ρ ℓ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto1 σ a K))
        op-push)
   
   (--> ((begin E_0 E_1) ρ σ K)
        (E_0 ρ σ_0 (beg E_1 ρ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto1 σ a K))
        beg-push)
   
   (--> ((let x E_0 E_1) ρ σ K)
        (E_0 ρ σ_0 (let x E_1 ρ a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto1 σ a K))
        let-push)
   
   (--> ((C <= ℓ_1 ℓ_2 x ℓ_3 E) ρ σ K)
        ((C <= ℓ_1 ℓ_2 V ℓ_3 E) ρ σ K)
        (where (D_0 ... (V ρ_0) D_1 ...)
               (sto-lookup σ (env-lookup ρ x)))
        chk-subst)
   
   (--> ((C <= ℓ_1 ℓ_2 V-or-AE ℓ_3 E) ρ σ K)
        (E ρ σ_0 (chk C ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        (where (a) (alloc σ (K)))
        (where σ_0 (extend-sto1 σ a K))
        chk-push)))

(define (∆ Ms)
  (reduction-relation
   CESK* #:domain ς
   (--> ((f ^ f) ρ σ K)
        ((-- PV) ρ σ K)
        (where (M_1 ... (module f C PV) M_2 ...) ,Ms)
        Δ-self)
   (--> ((f ^ ℓ) ρ σ K)
        ((C <= f ℓ (-- PV) f (-- PV)) ρ σ K)
        (where (M_1 ... (module f C PV) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f) (term ℓ))))
        Δ-other)))

(define (Δ~ Ms)
  (union-reduction-relations
   (∆ Ms)
   (reduction-relation
    CESK* #:domain ς
    (--> ((f ^ ℓ) ρ σ K)
         ((C <= f ℓ (-- C) f (-- C)) ρ σ K)
         (where (M_1 ... (module f C ☁) M_2 ...) ,Ms)
         (side-condition (not (eq? (term f) (term ℓ))))
         ∆-opaque))))

(define error-propagate
  (reduction-relation 
   CESK* #:domain ς
   (--> (B ρ σ K) (B () (gc (B () σ mt)) mt)
        (side-condition (not (equal? (term K) (term mt))))
        halt-blame)))

(define (stepΔ Ms)
  (union-reduction-relations error-propagate step (Δ~ Ms)))

(define-metafunction CESK*
  restrict : ((any any) ...) (any ...) -> ((any any) ...)
  [(restrict any_l any_keys)
   ,(for/list ([e (in-list (term any_l))]
               #:when (member (car e) (term any_keys)))
      e)])

(define-metafunction CESK*
  live-loc-clo : (E ρ) -> (a ...)
  [(live-loc-clo (E ρ))
   (a_0 ... a_1 ...)
   (where (a_0 ...) (live-loc-E E))
   (where (a_1 ...) (live-loc-env (restrict ρ (fv E))))])

(define-metafunction CESK*
  live-loc-env : ρ -> (a ...)
  [(live-loc-env ((x a) ...))
   (a ...)])

(define-metafunction CESK*
  live-loc-E : any_E -> (a ...)
  [(live-loc-E (addr a)) (a)]
  [(live-loc-E (any ...))
   (a ... ...)
   (where ((a ...) ...) ((live-loc-E any) ...))]
  [(live-loc-E any) ()])

(define-metafunction CESK*
  live-loc-K : K -> (a ...) 
  [(live-loc-K mt) ()]
  [(live-loc-K (ap clo ... E ... ρ ℓ a)) 
   (a a_0 ... ... a_1 ... ...)
   (where ((a_0 ...) ...) ((live-loc-clo clo) ...))
   (where ((a_1 ...) ...) ((live-loc-clo (E ρ)) ...))] 
  [(live-loc-K (if E_1 E_2 ρ a)) 
   (a a_0 ... a_1 ...)
   (where (a_0 ...) (live-loc-clo (E_1 ρ)))
   (where (a_1 ...) (live-loc-clo (E_2 ρ)))]    
  [(live-loc-K (op o clo ... E ... ρ ℓ a)) 
   (a a_0 ... ... a_1 ... ...)
   (where ((a_0 ...) ...) ((live-loc-clo clo) ...))
   (where ((a_1 ...) ...) ((live-loc-clo (E ρ)) ...))]
  [(live-loc-K (let x E ρ a))
   (a a_0 ...)
   (where (a_0 ...) (live-loc-clo (E ρ)))]
  [(live-loc-K (beg E ρ a))
   (a a_0 ...)
   (where (a_0 ...) (live-loc-clo (E ρ)))]
  ;; Probably want V-or-AE to be a closure and traverse it as well.
  [(live-loc-K (chk C ℓ_0 ℓ_1 V-or-AE ℓ_2 a))
   (a)]
  [(live-loc-K (dem AV a))
   (a a_0 ...)
   (where (a_0 ...) (live-loc-E AV))])

(define-metafunction CESK*
  live-loc-Ds : (D ...) -> (a ...)
  [(live-loc-Ds ()) ()]
  [(live-loc-Ds ((V ρ) D ...))
   (a_0 ... a_1 ...)
   (where (a_0 ...) (live-loc-clo (V ρ)))
   (where (a_1 ...) (live-loc-Ds (D ...)))]
  [(live-loc-Ds (K D ...))
   (a_0 ... a_1 ...)
   (where (a_0 ...) (live-loc-K K))
   (where (a_1 ...) (live-loc-Ds (D ...)))])

(define-metafunction CESK*
  reachable : (a ...) (a ...) σ -> (a ...)
  [(reachable () (a ...) σ) (a ...)]
  [(reachable (a a_0 ...) (a_1 ...) σ)   
   (reachable (set-minus (a_0 ... a_2 ...) (a a_1 ...))
              (a a_1 ...)
              σ)
   (where (a_2 ...) (live-loc-Ds (sto-lookup σ a)))])

(define-metafunction CESK*
  gc : ς -> σ
  [(gc (E ρ σ K)) 
   (restrict σ (reachable (a_0 ... a_1 ...) () σ))
   (where (a_0 ...) (live-loc-clo (E ρ)))
   (where (a_1 ...) (live-loc-K K))])     

(define (size sexp)
  (if (not (cons? sexp))
      1
      (+ (size (car sexp))
         (size (cdr sexp))
         1)))


(define step-gc  
  (let ((count 0)
        (m 0)
        (seen (set)))    
    (reduction-relation 
     CESK* #:domain ς
     [--> ς_old (E ρ_1 σ_1 K)
          (where ((any_1 ς_1) ... (any_name (E ρ σ K))  (any_2 ς_2) ...)
                 ,(apply-reduction-relation/tag-with-names step (term ς_old)))
          (where σ_1 (gc (E ρ σ K)))
          (where ρ_1 (restrict ρ (fv E)))
          #;
          (side-condition (begin (set! count (add1 count))
                                 (set! seen (set-add seen (term (E ρ σ_1 K))))
                                 (when (> (size  (term (E ρ σ_1 K))) m)
                                   (printf "state: ~a~n" (term (E ρ σ_1 K))))                    
                                 (set! m (max m (size (term (E ρ σ_1 K)))))
                                 (when (zero? (modulo count 100))
                                   (printf "c: ~a, m: ~a, |s|: ~a ~n" count m (set-count seen)))))
          (computed-name (term any_name))])))

(define (stepΔ-gc Ms)
  (union-reduction-relations error-propagate step-gc (Δ~ Ms)))


(define ((colorize Ms) x node)
  (define opaques (filter-map (λ (M) (match M
                                       [`(module ,n ,c ☁) n]
                                       [_ #f]))
                              Ms))
  (cond [(redex-match CESK* (V any any_1 mt) x) "green"]
        [(redex-match CESK* (B any any_1 mt) x)
         (redex-let CESK*
                    ([(blame ℓ ℓ_0 V C-ext V_0) (car x)])
                    (cond [(equal? (term ℓ) '★) "pink"]
                          [(member (term ℓ) opaques) "pink"]
                          [else "red"]))]
        [(null? (term-node-children node)) "blue"]
        [else #t]))

(define-syntax-rule (trace-it P . rest)
  (traces (stepΔ-gc (all-but-last P))
          (term (load ,(last P)))
          #:pred (colorize (all-but-last P))
          . rest))

#|
(trace-it fit-example)
(trace-it fit-example-rsa-7)
(trace-it fit-example-keygen-string)
(trace-it example-8)
(trace-it example-8-opaque)
(trace-it list-id-example)
(trace-it (term (ann ,cons/c-example-raw)))
|#

(define-syntax (print-here stx)
  (syntax-case stx ()
    [(_ foo)
     #`(displayln #,(syntax-line #'foo))]))

(define-syntax-rule (test-->>p P e ...)
  (begin (print-here P)
  (test-->>E (stepΔ-gc (all-but-last P))
            ;#:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2))))
            ;#:cycles-ok
            (term (load ,(last P)))
            (term (load ,e))) ...))

(define-syntax-rule (test-->>pE P e ...)
  (test-->>E (stepΔ-gc (all-but-last P))
             #;#;
             #:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2))))
             (term (load ,(last P)))
             (term (load ,e)) ...))

(define-syntax-rule (test-->>c r t1 t2)
  (test-->> r #:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2)))) (term (load ,t1)) (term (load ,t2))))

(test
 (test-->>c step (term (@ (-- (λ (x) 0)) (-- 1) †)) (term (-- 0)))
 #; ;; this loops
 (test-->>c v 
            (term (@ (-- (λ f (x) (@ f x †))) (-- 0) †))
            (term (@ (-- (λ f (x) (@ f x †))) (-- 0) †))) 
 
 (test-->>c step (term (@ (-- 0) (-- 1) †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test-->>c step (term (if (-- 0) 1 2)) (term (-- 1)))
 (test-->>c step (term (if (-- #t) 1 2)) (term (-- 1)))
 (test-->>c step (term (if (-- #f) 1 2)) (term (-- 2)))
 (test-->>c step (term (@ add1 (-- 0) †)) (term (-- 1)))
 (test-->>c step (term (@ proc? (-- #f) †)) (term (-- #f)))
 (test-->>c step (term (@ proc? (-- (λ (x) x)) †)) (term (-- #t)))
 (test-->>c step (term (@ proc? (-- (λ f (x) x)) †)) (term (-- #t)))
 (test-->>c step (term (@ proc? (-- ((any/c) -> (any/c))) †)) (term (-- #t)))
 (test-->>c step (term (@ cons (-- 1) (-- 2) †)) (term (-- (cons (-- 1) (-- 2)))))
 
 (test-->>c step (term (@ (λ (x) 0) 1 †)) (term (-- 0)))                
 (test-->>c step (term (@ 0 1 †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test-->>c step (term (if 0 1 2)) (term (-- 1)))
 (test-->>c step (term (if #t 1 2)) (term (-- 1)))
 (test-->>c step (term (if #f 1 2)) (term (-- 2)))
 (test-->>c step (term (@ add1 0 †))  (term (-- 1)))
 (test-->>c step (term (@ proc? #f †)) (term (-- #f)))
 (test-->>c step (term (@ cons 1 2 †)) (term (-- (cons (-- 1) (-- 2))))))


(test
 (test-->>c step (term (@ (λ () 4) f)) (term (-- 4)))
 (test-->>c step (term (@ (λ z () 4) f)) (term (-- 4)))
 (test-->>c step (term (@ (-- (-> (nat/c))) f)) (term (-- (nat/c))))
 (test-->>c step (term ((nat/c) <= f g (-- 0) f (-- 5))) (term (-- 5)))
 (test-->>c step 
            (term ((nat/c) <= f g (-- 0) f (-- (λ (x) x))))
            (term (blame f f (-- 0) (nat/c) (-- (λ (x) x)))))
 (test-->>c step 
            (term ((nat/c) <= f g (-- 0) f (-- #t))) 
            (term (blame f f (-- 0) (nat/c) (-- #t))))
 (test-->>c step 
            (term (((any/c)  -> (any/c)) <= f g (-- 0) f (-- (λ (x) x))))
            (term (-- (λ (z) ((any/c) <= f g (-- 0) f 
                                      (@ (-- (λ (x) x)) ((any/c) <= g f z f z) Λ))))))
 (test-->>c step 
            (term (((any/c)  -> (any/c)) <= f g (-- 0) f (-- 5)))
            (term (blame f f (-- 0) ((any/c) -> (any/c)) (-- 5))))
 (test-->>c step
            (term ((pred (λ (x) 0) ℓ) <= f g (-- 0) f (-- 5)))
            (term (-- 5 (pred (λ (x) 0) ℓ))))
 (test-->>c step
            (term ((and/c (nat/c) (empty/c)) <= f g (-- 0) f (-- #t)))
            (term (blame f f (-- 0) (nat/c) (-- #t)))))






(test 
 ;; testing demonic
 (test-->>pE (term (ann [(module p ((cons/c nat? nat?) -> nat?) ☁)
                         (p (cons 1 2))]))
             (term (-- (pred nat? p)))) 
 (test-->>p (term (ann [(module p ((and/c nat? nat?) -> nat?) ☁)
                        (p 1)]))
            (term (-- (pred nat? p))))
 (test-->>p (term (ann [(module p ((or/c nat? nat?) -> nat?) ☁)
                        (p 1)]))
            (term (-- (pred nat? p)))) 
 (test-->>p (term [((string/c) <= |†| rsa (-- "Plain") rsa (-- "Plain"))])
            (term (-- "Plain"))) 
 (test-->>p (term [(@ (-- (λ (o) (b ^ o))) (-- "") sN)])
            (term (b ^ o))) 
 (test-->>p (term [(@ (-- (λ (o) (@ 4 5 o))) (-- "") sN)])
            (term (blame o Λ (-- 4) λ (-- 4)))) 
 (test-->>p (term (ann [(module n (and/c nat? nat?) 1) n]))
            (term (-- 1))) 
 (test-->>p (term (ann [(module n (and/c nat? (pred (λ (x) (= x 7)))) 7) n]))
            (term (-- 7 (pred (λ (x) (@ = x 7 n)) n)))) 
 (test-->>p (term (ann [(module n (and/c nat? (pred (λ (x) (= x 8)))) 7) n]))
            (term (blame n n (-- 7) (pred (λ (x) (@ = x 8 n)) n) (-- 7))))
 (test-->>p (term (ann [(module n (and/c nat? (pred (λ (x) (= x 8)))) "7") n]))
            (term (blame n n (-- "7") (pred nat? n) (-- "7"))))
 (test-->>p fit-example (term (-- (pred string? rsa))))
 (test-->>p fit-example-keygen-string
            (term (blame keygen prime? (-- "Key") (pred nat? prime?) (-- "Key"))))
 (test-->>p fit-example-rsa-7
            (term (-- (pred string? rsa)))
            (term (blame keygen keygen (-- (λ (x) 7)) (pred (prime? ^ keygen) keygen) (-- 7)))) 
 (test-->>p example-8 (term (blame h g (-- #f) (pred (λ (x) x) g) (-- #f))))
 (test-->>p example-8-opaque 
            (term (-- (any/c)))
            (term (blame h g (-- (any/c)) (pred (λ (x) x) g) (-- (any/c)))))
 (test-->>p list-id-example (term (-- (cons (-- 1) 
                                            (-- (cons (-- 2) 
                                                      (-- (cons (-- 3) (-- empty))))))))) 
 (test-->>p (term (ann ,list-rev-example-raw))
            (term (-- (cons (-- 3)
                            (-- (cons (-- 2)
                                      (-- (cons (-- 1)
                                                (-- empty)))))))))
 
 ;; Not sure about the remembered contracts in these examples. 
 (test-->>p (term (ann [(module n nat? 5) n]))
            (term (-- 5))) 
 (test-->>p (term (ann [(module p
                          (cons/c nat? nat?)
                          (cons (-- 1) (-- 2)))
                        p]))
            (term (-- (cons (-- 1) (-- 2)) 
                      (cons/c (pred nat? p) (pred nat? p)))))
 (test-->>p (term (ann [(module p
                          (pred (λ (x) (if (cons? x)
                                           (= (first x)
                                              (rest x))
                                           #f)))
                          (cons (-- 1) (-- 1)))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (pred (λ (x) (if (@ cons? x p)
                                       (@ = 
                                          (@ first x p)
                                          (@ rest x p)
                                          p)
                                       #f))
                            p))))
 (test-->>p (term (ann [(module p
                          (and/c (cons/c nat? nat?)
                                 (pred (λ (x) (= (first x) (rest x)))))
                          (cons (-- 1) (-- 1)))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (cons/c (pred nat? p) (pred nat? p)) 
                      (pred (λ (x) (@ = (@ first x p) (@ rest x p) p)) p))))
 
 ;; Swap of and/c arguments above
 (test-->>p (term (ann [(module p
                          (and/c (pred (λ (x) (= (first x) (rest x))))
                                 (cons/c nat? nat?))                                
                          (cons (-- 1) (-- 1)))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (pred (λ (x) (@ = (@ first x p) (@ rest x p) p)) p)
                      (cons/c (pred nat? p) (pred nat? p)))))
 
 (test-->>p (term (ann [(module p
                          (cons/c nat? nat?)
                          (cons (-- 1) (-- 2)))
                        (first p)]))
            (term (-- 1)))
 (test-->>p (term (ann [(module p
                          (cons/c nat? nat?)
                          (cons (-- "hi") (-- 2)))
                        (first p)]))
            (term (blame p p (-- (cons (-- "hi") (-- 2))) (pred nat? p) (-- "hi"))))
 
 (test-->>p (term (ann [(module p
                          (cons/c (anything -> nat?) anything)
                          (cons (-- (λ (x) "hi"))
                                (-- 7)))
                        ((first p) 7)]))
            (term (blame p p (-- (cons (-- (λ (x) "hi"))
                                       (-- 7)))
                         (pred nat? p)
                         (-- "hi"))))
 
 
 (test-->>p (term [(module mt-val (pred empty? mt-val) empty) (mt-val ^ †)])
            (term (-- empty)))
 
 (test-->>p list-id-example-contract
            (term (-- (cons (-- 1)
                            (-- (cons (-- 2)
                                      (-- (cons (-- 3)
                                                (-- empty))))))
                      ,list-of-nat/c)))
 )

(define fact-prog
  (term ((module fact (nat? -> nat?)
           (λ f (x) (if (= x 0) 1 (* x (f (sub1 x))))))
         (module input nat? ☁)         
         (fact input))))

(define wrong-prog
  (term ((module fact (nat? -> nat?)
           (λ f (x) (if (= (add1 x) (add1 0)) 1 (* x (f (sub1 x))))))
         (module input nat? ☁)         
         (fact input))))

(define fit-ex-prog
  (term ((module prime? (anything -> bool?) ☁)
         (module keygen (anything -> (pred prime?)) ☁) 
         (module rsa ((pred prime?) -> (string? -> string?)) ☁)
         ((rsa (keygen #f)) "Plain"))))

(define (final P)
  (apply-reduction-relation* (stepΔ-gc (all-but-last P))
                             (term (load ,(last P)))
                             #:cache-all? #t))

(define next #f)
(define result #f)

(define (single P)
  (set! next (λ () 
               (define r (append-map (λ (p) (apply-reduction-relation (stepΔ-gc (all-but-last P)) p)) result))
               (set! result r)
               r))
  (let ([r (apply-reduction-relation (stepΔ-gc (all-but-last P))
                                     (term (load ,(last P))))])
    (set! result r)
    r))


;; Doesn't terminate, but should
;(final (term (ann ,wrong-prog)))
;(trace-it (term (ann ,wrong-prog)))
