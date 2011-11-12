#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test meta-misc)

;; a really dumb little partial evaluator
(define-metafunction λcρ
  @@ : any any ... LAB -> any
  [(@@ (λ (X) EXP) X LAB) EXP]
  [(@@ (λ (X) #t) EXP LAB) (begin EXP #t)]
  [(@@ (λ (X) #f) EXP LAB) (begin EXP #f)]
  [(@@ any ... LAB) (@ any ... LAB)])

(define-metafunction λcρ
  IFF : any any any -> any
  [(IFF #f any_1 any_2) any_2]
  [(IFF #t any_1 any_2) any_1]
  [(IFF any_0 any_1 any_2) (if any_0 any_1 any_2)])

(define-metafunction λcρ
  AND : any ... -> any
  [(AND any) any]
  [(AND any any_1) (IFF any any_1 #f)]
  [(AND any any_1 ...) (IFF any (AND any_1 ...) #f)])

(define current-direct? (make-parameter #t))
;; Interp: direct? => doesn't go through store.

(define-metafunction λcρ
  bind-vars : ρ σ (X V) ... -> (ρ σ)
  [(bind-vars ρ σ (X V) ...)
   (ρ_1 σ_1)
   (where (a ...) (alloc σ (X ...)))
   (where σ_1 (extend-sto* σ (a (V)) ...))
   (where ρ_1 (extend-env* ρ (X a) ...))   
   (side-condition (not (current-direct?)))]
  [(bind-vars ρ σ (X V) ...)
   (ρ_1 σ)
   (where ρ_1 (extend-env* ρ (X V) ...))])

(define-metafunction λcρ
  lookup-var : σ ρ X -> (V ...)
  [(lookup-var σ ρ X) 
   (sto-lookup σ (env-lookup ρ X))
   (side-condition (not (current-direct?)))]
  [(lookup-var σ ρ X)
   ((env-lookup ρ X))])


(define-metafunction λcρ
  fv : EXP -> (side-condition any_s (set? (term any_s)))
  [(fv (λ (X ...) EXP))
   ,(set-subtract (term (fv EXP)) (apply set (term (X ...))))]
  [(fv (λ X_1 (X_2 ...) EXP))
   ,(set-subtract (term (fv EXP)) (apply set (term (X_1 X_2 ...))))]
  [(fv (cons VAL_1 VAL_2)) 
   ,(set-union (term (fv VAL_1))
               (term (fv VAL_2)))]
  [(fv VAL) ,(set)]
  [(fv X) ,(set (term X))]
  [(fv MODREF) ,(set)]
  [(fv PRIMREF) ,(set)]
  [(fv (@ EXP ... LAB))
   ,(apply set-union (term ((fv EXP) ...)))]
  [(fv (if EXP ...))
   ,(apply set-union (term ((fv EXP) ...)))]
  [(fv (let ((X EXP) ...) EXP_1))
   ,(apply set-union (set-subtract (term (fv EXP_1)) (apply set (term (X ...))))
           (term ((fv EXP) ...)))]
  [(fv (begin EXP ...))
   ,(apply set-union (term ((fv EXP) ...)))]
  [(fv •) ,(set)])

(test
 ;; totality check
 #;
 (redex-check λcρ EXP (set? (term (fv EXP)))))

(define-metafunction λcρ
  restrict : EXP ρ -> ρ
  [(restrict EXP ρ)
   ,(for/hash ([(k v) (term ρ)]
               #:when (set-member? (term (fv EXP)) k))
      (values k v))])

(test
 (test-equal (term (restrict empty (env (x 0)))) (term (env)))
 (test-equal (term (restrict x (env (x 0)))) (term (env (x 0)))))

(define-metafunction λcρ
  ↓ : EXP ρ -> D
  [(↓ EXP ρ) (clos EXP (restrict EXP ρ))])

(test
 (test-equal (term (↓ x (env (x 0))))
             (term (clos x (env (x 0))))))

(define-metafunction λcρ
  env : (X any) ... -> ρ
  [(env (X any) ...)
   ,(apply hash (apply append (term ((X any) ...))))])


(define-metafunction λcρ
  sto : (any (V ...)) ... -> σ
  [(sto (any (V ...)) ...)
   ,(apply hash (apply append 
                       (map (λ (k+vs) (list (first k+vs) (apply set (second k+vs))))
                            (term ((any (V ...)) ...)))))])
(define-metafunction λcρ
  alloc : σ (any ..._1) -> (a ..._1)
  [(alloc σ (any ...))
   ((loc any_1) ...)
   (where (any_1 ...) ,(alloc-addr (term σ) (term (any ...))))])

(define (alloc-addr σ vals)
   (cond [(current-exact?) (variables-not-in* (hash-keys σ) vals)]
         [(andmap symbol? vals)
          #;
          (variables-not-in (hash-keys σ) vals)
          vals]
         ;; FIXME
         #;
         [(andmap V? vals)
          (build-list (length vals) values)]
         [else ;; continuations
          (map (λ (p) (if (list? p) (drop-right p 1) p)) vals)]))

(define-metafunction λcρ
  extend-env* : ρ (X any) ... -> ρ
  [(extend-env* ρ) ρ]
  [(extend-env* ρ (X any) (X_1 any_1) ...)
   (extend-env* (extend-env ρ X any) (X_1 any_1) ...)])

(define-metafunction λcρ
  extend-env : ρ X any -> ρ
  [(extend-env ρ X any)
   ,(hash-set (term ρ) (term X) (term any))])

(test 
 (test-equal (term (extend-env (env) x (loc 0)))
             (hash 'x '(loc 0))))

(define-metafunction λcρ
  extend-sto* : σ (a (any ...)) ... -> σ
  [(extend-sto* σ) σ]
  [(extend-sto* σ (a (any ...)) (a_1 (any_1 ...)) ...)
   (extend-sto* (extend-sto σ a (any ...)) (a_1 (any_1 ...)) ...)])

(define-metafunction λcρ
  extend-sto : σ any (any ...) -> σ
  [(extend-sto σ any_a (any ...))
   ,(hash-set (term σ) (term any_a)
              (set-union (apply set (term (any ...)))
                         (hash-ref (term σ) (term any_a) (set))))])

(test
 (test-equal (term (extend-sto ,(hash) (loc 0) (x y z)))
             (hash '(loc 0) (set 'x 'y 'z)))
 (test-equal (term (extend-sto ,(hash '(loc 0) (set 'x 'y 'z)) (loc 0) (q)))
             (hash '(loc 0) (set 'x 'y 'z 'q))))

(define-metafunction λcρ
  env-lookup : ρ X -> any
  [(env-lookup ρ X)
   ,(hash-ref (term ρ) (term X))])

(define (set->list s) (for/list ([x (in-set s)]) x))

(define-metafunction λcρ
  sto-lookup : σ any -> (any ...)
  [(sto-lookup σ any)
   ,(set->list (hash-ref (term σ) (term any)))])
    
(define-metafunction λcρ
  explode : C -> (C ...)
  [(explode ((or/c CON_1 CON_2) ρ))
   (C_1e ... C_2e ...)
   (where ((C_1e ...) (C_2e ...)) ((explode (CON_1 ρ)) (explode (CON_2 ρ))))]  
  [(explode ((rec/c X CON) ρ))            ;; Productive implies you'll never get
   (explode ((unroll (rec/c X CON)) ρ))]  ;; back to (rec/c x C) in this metafunction.   
  [(explode C) (C)])

(test
 (test-equal (term (explode ((∧) (env))))
             (term (((∧) (env)))))
 (test-equal (term (explode ((or/c (∧) (∧)) (env))))
             (term (((∧) (env)) ((∧) (env)))))
 (test-equal (term (explode ((rec/c x (∧)) (env))))
             (term (((∧) (env)))))) 

(define-metafunction λcρ
  unroll : (rec/c X CON) -> CON
  [(unroll (rec/c X CON))
   (subst/μ X (rec/c X CON) CON)])

(test
 #;
 (redex-check λc-user (X CON) 
              (equal? (term (unroll (rec/c X CON)))
                      (term (subst/μ X (rec/c X CON) CON)))))

(define-metafunction λcρ 
  ∈ : any (any ...) -> #t or #f
  [(∈ any (any_0 ... (-- any) any_1 ...)) #t]
  [(∈ any (any_0 ... (-- (clos any ρ) C ...) any_1 ...)) #t]
  [(∈ any_0 any_1) #f])

;; If there are multiple arrows, we (arbitrarily) take the first arity.
;; Does this value *definitely* include the given arity?
(define-metafunction λcρ
  arity-includes? : V natural -> #t or #f
  [(arity-includes? (-- (clos apply ρ) C ...) 2) #t]
  [(arity-includes? (-- (clos OP0* ρ) C ...) natural) #t]
  [(arity-includes? (-- (clos OP1 ρ) C ...) 1) #t]
  [(arity-includes? (-- (clos OP2 ρ) C ...) 2) #t]
  [(arity-includes? (-- (clos (s-pred X_m X_tag) ρ) C ...) 1) #t]
  [(arity-includes? (-- (clos (s-ref X_m X_tag natural) ρ) C ...) 1) #t]
  [(arity-includes? (-- (clos (s-cons X_m X_tag natural) ρ) C ...) natural) #t]
  
  [(arity-includes? (-- (clos (λ X (X_0 ...) EXP) ρ) C ...) natural)
   ,(= (length (term (X_0 ...))) (term natural))]
  [(arity-includes? (-- (clos (λ (X ...) EXP) ρ) C ...) natural)
   ,(= (length (term (X ...))) (term natural))]
  ;; ABSTRACT VALUES  
  [(arity-includes? (-- ((CON_0 ... -> CON_1) ρ) C ...) natural)
   ,(= (length (term (CON_0 ...))) (term natural))]
  [(arity-includes? (-- ((CON_0 ... -> (λ (X ...) CON_1)) ρ) C ...) natural)
   ,(= (length (term (CON_0 ...))) (term natural))]
  [(arity-includes? (-- C) natural) #f]
  [(arity-includes? (-- C_0 C ...) natural)
   (arity-includes? (-- C ...) natural)]
  [(arity-includes? ((CON ... --> any) ρ <= LAB_0 LAB_1 V_b LAB_2 any_0) natural)
   ,(= (length (term (CON ...))) (term natural))]
  [(arity-includes? (-- (clos (λ* (X ... X_r) EXP) ρ) C ...) natural)
   ,(<= (length (term (X ...))) (term natural))]
  [(arity-includes? ((CON ... CON_r -->* any) ρ <= LAB_0 LAB_1 V_b LAB_2 any_0) natural)
   ,(<= (length (term (CON ...))) (term natural))])

(test
 (test-equal (term (arity-includes? (-- (↓ (λ () x) (env))) 0)) #t)
 (test-equal (term (arity-includes? (-- (↓ (λ (x y z) x) (env))) 3)) #t)
 (test-equal (term (arity-includes? (-- (↓ (λ f (x y z) x) (env))) 3)) #t)
 (test-equal (term (arity-includes? (-- (((pred string? f) (pred string? g) -> (pred string? h)) (env))) 2)) #t)
 (test-equal (term (arity-includes? (-- (((pred string? f) (pred string? g) -> (λ (x y) (pred string? h))) (env))) 2)) #t)
 (test-equal (term (arity-includes? (-- ((pred string? h) (env)) (((pred string? f) (pred string? g) -> (pred string? h)) (env))) 2)) #t)
 (test-equal (term (arity-includes? (-- ((pred procedure? f) (env))) 8)) #f)
 (test-equal (term (arity-includes? ((--> (pred string? †)) (env) <= f g (-- (↓ 0 (env))) f (-- (↓ (λ () 1) (env)))) 0)) #t)
 (test-equal (term (arity-includes? (-- (↓ (λ* (x y) x) (env))) 0)) #f)
 (test-equal (term (arity-includes? (-- (↓ (λ* (x y) x) (env))) 1)) #t)
 (test-equal (term (arity-includes? (-- (↓ (λ* (x y) x) (env))) 100)) #t)
 )

;; Is C_1 /\ C_2 inhabited
(define-metafunction λcρ
  feasible : C C -> #t or #f
  [(feasible ATOMC CONSC) #f]
  [(feasible CONSC ATOMC) #f]
  [(feasible NOTPROCC ARROWC) #f]
  [(feasible ARROWC NOTPROCC) #f]  
  [(feasible ATOMC_1 ATOMC_2) 
   ,(or (term (implies ATOM?_1 ATOM?_2))
        (term (implies ATOM?_2 ATOM?_1)))
   (where ((pred ATOM?_1 LAB_1) ρ_1) ATOMC_1)
   (where ((pred ATOM?_2 LAB_2) ρ_2) ATOMC_2)]
  [(feasible ((atom/c any_1 LAB_1) ρ_1) ((atom/c any_2 LAB_2) ρ_2)) 
   ,(eqv? (term any_1) (term any_2))]
  [(feasible C_1 C_2) #t])

(define-metafunction λcρ
  implies : ATOM? ATOM? -> #t or #f
  [(implies ATOM? ATOM?) #t]
  [(implies zero? exact-nonnegative-integer?) #t]  
  [(implies false? boolean?) #t]
  [(implies ATOM?_1 ATOM?_2) #f])

(define-metafunction λcρ
  join-contracts : C ... -> AV
  [(join-contracts C ...)
   (remember-contract (-- ((pred (λ (x) #t) Λ) (env))) C ...)])

(test 
 (test-equal (term (join-contracts))
             (term (-- ((pred (λ (x) #t) Λ) (env)))))
 (test-equal (term (join-contracts ((pred boolean? †) (env))))
             (term (-- ((pred boolean? †) (env))))))

(define-metafunction λcρ
  ∧ : CON ... -> CON
  [(∧)  (pred (λ (x) #t) Λ)]
  [(∧ CON) CON]
  [(∧ CON_0 CON_1  ...)
   (and/c CON_0 (∧ CON_1 ...))])

(test
 (test-equal (term (∧)) (term (pred (λ (x) #t) Λ)))
 (test-equal (term (∧ (pred boolean? †)))
             (term (pred boolean? †)))
 (test-equal (term (∧ (pred boolean? †) (pred string? †)))
             (term (and/c (pred boolean? †)
                          (pred string? †)))))

(define-metafunction λcρ
  modref=? : MODREF MODREF -> #t or #f
  [(modref=? (X ^ LAB_1 X_1) (X ^ LAB_2 X_1)) #t]
  [(modref=? MODREF_1 MODREF_2) #f])

(define-judgment-form λcρ
  #:mode (≡C I I)
  #:contract (≡C C C)
  [(≡C C C)]
  [(≡C ((atom/c ATOMLIT LAB_1) ρ_1)
       ((atom/c ATOMLIT LAB_2) ρ_2))]
  [(≡C ((pred MODREF_1 LAB_1) ρ_1)
       ((pred MODREF_2 LAB_2) ρ_2))
   (where #t (modref=? MODREF_1 MODREF_2))]
  ;; FIXME maybe want to do ≡α here.
  [(≡C ((pred PREDV LAB_1) ρ)
       ((pred PREDV LAB_2) ρ))]
  [(≡C ((and/c CON_1 CON_2) ρ_1)
       ((and/c CON_3 CON_4) ρ_2))
   (≡C (CON_1 ρ_1) (CON_3 ρ_2))
   (≡C (CON_2 ρ_1) (CON_4 ρ_2))]  
  [(≡C ((and/c CON_1 CON_2) ρ_1) 
       ((and/c CON_3 CON_4) ρ_2))
   (≡C (CON_1 ρ_1) (CON_4 ρ_2)) 
   (≡C (CON_2 ρ_1) (CON_3 ρ_2))]  
  [(≡C ((or/c CON_1 CON_2) ρ_1)
       ((or/c CON_3 CON_4) ρ_2))
   (≡C (CON_1 ρ_1) (CON_3 ρ_2))
   (≡C (CON_2 ρ_1) (CON_4 ρ_2))]
  [(≡C ((or/c CON_1 CON_2) ρ_1)
       ((or/c CON_3 CON_4) ρ_2))
   (≡C (CON_1 ρ_1) (CON_4 ρ_2))
   (≡C (CON_2 ρ_1) (CON_3 ρ_2))]
  [(≡C ((not/c CON_1) ρ_1)
       ((not/c CON_3) ρ_2))
   (≡C (CON_1 ρ_1) (CON_3 ρ_2))]
  ;; FIXME maybe want to do ≡α here and `equal?'-style "infinite" unrolling.
  [(≡C ((rec/c X CON_1) ρ_1) ((rec/c X CON_2) ρ_2))
   (≡C (CON_1 ρ_1) (CON_2 ρ_2))]
  [(≡C ((cons/c CON_1 CON_2) ρ_1) ((cons/c CON_3 CON_4) ρ_2))
   (≡C (CON_1 ρ_1) (CON_3 ρ_2))
   (≡C (CON_2 ρ_1) (CON_4 ρ_2))]
  [(≡C ((struct/c X_m X_tag CON_1 ...) ρ_1) ((struct/c X_m X_tag CON_2 ...) ρ_2))
   (≡C (CON_1 ρ_1) (CON_2 ρ_2)) 
   ...]
  [(≡C ((CON_1 ..._1 -> CON_2) ρ_1)
       ((CON_3 ..._1 -> CON_4) ρ_2))
   (≡C (CON_1 ρ_1) (CON_3 ρ_2)) 
   ...
   (≡C (CON_2 ρ_1) (CON_4 ρ_2))]  
  ;; FIXME maybe want to do ≡α
  [(≡C ((CON_1 ..._1 -> (λ (X ..._1) CON_2)) ρ_1)
       ((CON_3 ..._1 -> (λ (X ..._1) CON_4)) ρ_2))
   (≡C (CON_1 ρ_1) (CON_3 ρ_2)) 
   ... 
   (≡C (CON_2 ρ_1) (CON_4 ρ_2))])
  
  
(test 
 (test-equal (judgment-holds (≡C ((∧) (env)) ((∧) (env)))) #t)
 (test-equal (judgment-holds (≡C ((pred (f ^ g h) r) (env)) 
                                 ((pred (f ^ j h) s) (env))))
             #t)
 (test-equal (judgment-holds (≡C ((and/c (pred (f ^ g h) r)
                                         (pred (q ^ w x) u)) (env))
                                 ((and/c (pred (q ^ y x) t)
                                         (pred (f ^ j h) s)) (env))))
             #t)
 (test-equal (judgment-holds (≡C ((and/c (pred (q ^ w x) u)
                                         (pred (f ^ g h) r)) (env))
                                 ((and/c (pred (q ^ y x) t)
                                         (pred (f ^ j h) s)) (env))))
             #t) 
 (test-equal (judgment-holds (≡C ((or/c (pred (f ^ g h) r)
                                        (pred (q ^ w x) u)) (env))
                                 ((or/c (pred (q ^ y x) t)
                                        (pred (f ^ j h) s)) (env))))
             #t)
 (test-equal (judgment-holds (≡C ((or/c (pred (q ^ w x) u)
                                        (pred (f ^ g h) r)) (env))
                                 ((or/c (pred (q ^ y x) t)
                                        (pred (f ^ j h) s)) (env))))
             #t)
 (test-equal (judgment-holds (≡C ((rec/c x (pred (f ^ g h) r)) (env)) 
                                 ((rec/c x (pred (f ^ j h) s)) (env))))
             #t)
 (test-equal (judgment-holds (≡C ((not/c (pred (f ^ g h) r)) (env)) 
                                 ((not/c (pred (f ^ j h) s)) (env))))
             #t)
 (test-equal (judgment-holds (≡C ((cons/c (pred (q ^ w x) u) (pred (f ^ g h) r)) (env))
                                 ((cons/c (pred (q ^ y x) t) (pred (f ^ j h) s)) (env))))
             #t)
 (test-equal (judgment-holds (≡C ((struct/c p posn) (env)) ((struct/c p posn) (env))))
             #t)                                                                                         
 (test-equal (judgment-holds (≡C (((pred (q ^ w x) u) -> (pred (f ^ g h) r)) (env))
                                 (((pred (q ^ y x) t) -> (pred (f ^ j h) s)) (env))))
             #t)
 (test-equal (judgment-holds (≡C (((pred (q ^ w x) u) -> (λ (x) (pred (f ^ g h) r))) (env))
                                 (((pred (q ^ y x) t) -> (λ (x) (pred (f ^ j h) s))) (env))))
             #t))
  
;; FIXME: don't need to remember arity-like contracts on arity-known procedures.
(define-metafunction λcρ
  remember-contract : V C ... -> V
  ;; Expand away and/c
  [(remember-contract V ((and/c CON_1 CON_2) ρ) C ...)
   (remember-contract V (CON_1 ρ) (CON_2 ρ) C ...)] 
  ;; drop boring contracts on concrete flat values
  #;
  [(remember-contract (-- FV C_1 ...) FC C ...)
   (remember-contract (-- FV C_1 ...) C ...)]
  [(remember-contract (-- PREVAL C_0 ...) ((pred OP LAB) ρ) C ...)
   (remember-contract (-- PREVAL C_0 ...) C ...)] 
  ;; drop any/c on the floor when possible
  [(remember-contract (-- C C_1 ... ((pred (λ (X) #t) LAB) ρ)) C_2 ...)
   (remember-contract (-- C C_1 ...) C_2 ...)] 
  [(remember-contract (-- ((pred (λ (X) #t) LAB) ρ) C C_1 ...) C_2 ...)
   (remember-contract (-- C C_1 ...) C_2 ...)]
  [(remember-contract (-- ((pred (λ (X) #t) LAB) ρ)) C C_2 ...)
   (remember-contract (-- C) C_2 ...)]
  [(remember-contract V ((pred (λ (X) #t) LAB) ρ) C_2 ...)
   (remember-contract V C_2 ...)]
  ;; do the real work
  ;; forget duplicates  
  [(remember-contract (-- any_0 C_0 ... C_A C_1 ...) C_B C_2 ...)   
   (remember-contract (-- any_0 C_0 ... C_A C_1 ...) C_2 ...)
   (judgment-holds (≡C C_A C_B))]  
  [(remember-contract (-- C_0 ... C_A C_1 ...) C_B C_2 ...)
   (remember-contract (-- C_0 ... C_A C_1 ...) C_2 ...)
   (judgment-holds (≡C C_A C_B))]
  ;; add feasible non-duplicates  
  [(remember-contract (-- C_1 ...) C_2 C ...)
   (remember-contract (-- C_1 ... C_2) C ...)
   (where (#t ...) ((feasible C_2 C_1) ...))] 
  [(remember-contract (-- PREVAL C_1 ...) C_2 C ...)
   (remember-contract (-- PREVAL C_1 ... C_2) C ...)
   (where (#t ...) ((feasible C_2 C_1) ...))]  
  ;; drop infeasible contracts
  [(remember-contract (-- any_0 C_1 ...) C_2 C ...)
   (remember-contract (-- any_0 C_1 ...) C ...)]   
  ;; push remembered contracts past blessed arrows
  [(remember-contract (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) C_0 ...)
   (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2
           (remember-contract V C_0 ...))]
  ;; FIXME pretty sure this case is dead or just for addresses.
  #;
  [(remember-contract ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 any_1) C_0 ...)
   ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 any_1)]  
  ;; we're done
  [(remember-contract V) V])

(define (xprod xs . rest)
  (if (empty? rest)
      (map list xs)
      (for*/list ([z (in-list (apply xprod rest))]
                  [x xs])
        (cons x z))))
;; handles remembering rec/c and or/c

(define-metafunction λcρ
  remember-contract/any : V C ... -> (V ...)
  [(remember-contract/any V C* ...)
   ((remember-contract V C* ...))]  
  [(remember-contract/any V C ... ((and/c CON_1 CON_2) ρ) C_1 ...)
   (remember-contract/any V C ... (CON_1 ρ) (CON_2 ρ) C_1 ...)]
  [(remember-contract/any V C ...)
   (V_1 ... ...)
   (where ((C_1 ...) ...)
          ,(apply xprod (term ((explode C) ...))))
   (where ((V_1 ...) ...)
          ((remember-contract/any V C_1 ...) ...))])

(test
 
 (test-equal (term (remember-contract/any (-- ((pred exact-nonnegative-integer? f) (env)))
                                          ((or/c (pred string? f) (pred boolean? f)) (env))))
             (term ((remember-contract (-- ((pred exact-nonnegative-integer? f) (env)))
                                       ((pred string? f) (env)))
                    (remember-contract (-- ((pred exact-nonnegative-integer? f) (env)))
                                       ((pred boolean? f) (env))))))
 (test-equal (term (remember-contract/any (-- ((pred exact-nonnegative-integer? f) (env)))
                                          ((and/c (pred empty? f) (or/c (pred string? f) (pred boolean? f))) (env))))
             (term ((remember-contract (-- ((pred exact-nonnegative-integer? f) (env)))
                                       ((pred empty? f) (env)) ((pred string? f) (env)))
                    (remember-contract (-- ((pred exact-nonnegative-integer? f) (env)))
                                       ((pred empty? f) (env)) ((pred boolean? f) (env))))))
 
 ;; flatten and/c
 (test-equal (term (remember-contract (-- ((pred string? f) (env)))
                                      ((and/c (pred (f? ^ f g) m)
                                              (pred (h? ^ h j) n))
                                       (env))))
             (term (-- ((pred string? f) (env))
                       ((pred (f? ^ f g) m) (env))
                       ((pred (h? ^ h j) n) (env)))))
 ;; infeasible
 (test-equal (term (remember-contract (-- ((pred string? f) (env))) ((pred zero? g) (env))))
             (term (-- ((pred string? f) (env)))))
 ;; feasible
 (test-equal (term (remember-contract (-- ((pred exact-nonnegative-integer? f) (env))) ((pred zero? g) (env))))
             (term (-- ((pred exact-nonnegative-integer? f) (env))
                       ((pred zero? g) (env)))))
 ;; drop any
 (test-equal (term (remember-contract (-- ((pred string? f) (env))) ((pred (λ (x) #t) g) (env))))
             (term (-- ((pred string? f) (env)))))
 (test-equal (term (remember-contract (-- ((pred string? f) (env))
                                          ((pred (λ (x) #t) g) (env)))))
             (term (-- ((pred string? f) (env)))))
 (test-equal (term (remember-contract (-- ((pred (λ (x) #t) g) (env))
                                          ((pred string? f) (env)))))
             (term (-- ((pred string? f) (env)))))
 (test-equal (term (remember-contract (-- ((pred (λ (x) #t) g) (env)))
                                      ((pred string? f) (env))))
             (term (-- ((pred string? f) (env)))))
 
 ;; drop duplicates
 (test-equal (term (remember-contract (-- ((pred (p? ^ f g) f) (env))) ((pred (p? ^ f g) f) (env))))
             (term (-- ((pred (p? ^ f g) f) (env)))))
 (test-equal (term (remember-contract (-- (↓ 0 (env)) 
                                          ((pred (p? ^ f g) f) (env)))
                                      ((pred (p? ^ f g) f) (env))))
             (term (-- (↓ 0 (env)) 
                       ((pred (p? ^ f g) f) (env)))))
 
 ;; push past blessed arrow
 (test-equal (term (remember-contract ((--> (pred (p? ^ f g) f))
                                       (env) <= f g (-- (↓ 0 (env))) f 
                                       (-- (↓ (λ () "x") (env))))
                                      ((pred (q? ^ h j) f) (env))))
             (term ((--> (pred (p? ^ f g) f))
                    (env) <= f g (-- (↓ 0 (env))) f 
                    (-- (↓ (λ () "x") (env))
                        ((pred (q? ^ h j) f) (env)))))))

;; FIXME
#|
 ;; check that remember-contract is total and produces the right type
 (redex-check λc~ (V C ...)              
              (or (not (term (valid-value? V)))
                  (ormap not (term ((valid? C) ...)))
                  (redex-match λc~ V-or-AE (term (remember-contract V C ...)))))
|#

;; All domain contracts of all function contracts in given contracts.
;; produces a list of the list of contracts for each argument of a function.

;; In case of arity mismatch, we take the first function contract as canonical
;; just like `arity'.
(define-metafunction λcρ
  domain-contracts : (C ...) -> ((C ...) ...)
  [(domain-contracts (C ...))
   (domain-contracts* (C ...) ())])

(define-metafunction λcρ
  domain-contracts* : (C ...) ((C ...) ...) -> ((C ...) ...)
  [(domain-contracts* () any) any]
  [(domain-contracts* (((CON_1 ... -> any) ρ) C ...) ())
   (domain-contracts* (C ...) (((CON_1 ρ)) ...))]
  [(domain-contracts* (((CON_1 ..._1 -> any) ρ) C ...) ((C_3 ...) ..._1))
   (domain-contracts* (C ...) ((C_3 ... (CON_1 ρ)) ...))]
  [(domain-contracts* (C_0 C ...) any)
   (domain-contracts* (C ...) any)])

(test
  (test-equal (term (domain-contracts (((pred string? f) (env)))))
              (term ()))
  (test-equal (term (domain-contracts ((((pred exact-nonnegative-integer? f) 
                                         (pred string? f) -> 
                                         (pred exact-nonnegative-integer? f)) 
                                        (env))
                                       (((pred boolean? f) 
                                         (pred empty? f) -> 
                                         (pred exact-nonnegative-integer? f)) 
                                        (env)))))
              (term ((((pred exact-nonnegative-integer? f) (env)) ((pred boolean? f) (env)))
                     (((pred string? f) (env)) ((pred empty? f) (env)))))))

;; All range contracts of all function contracts in given contracts.
;; given the specified arguments for dependent contracts
;; throw out all ranges when the arity doesn't match the supplied number of values
(define-metafunction λcρ
  range-contracts : (C ...) (V ...) -> (C ...)
  [(range-contracts () any) ()]
  [(range-contracts (((CON_1 ..._1 -> CON_2) ρ) C ...) (V ..._1))
   ((CON_2 ρ) C_0 ...)
   (where (C_0 ...) (range-contracts (C ...) (V ...)))]
  [(range-contracts (((CON_1 ..._1 -> (λ (X ..._1) CON_2)) ρ) C ...) (V ..._1))
   ((CON_2 (env-extend ρ (X V) ...)) C_0 ...)
   (where (C_0 ...) (range-contracts (C ...) (V ...)))]
  [(range-contracts (C_0 C ...) any) 
   (range-contracts (C ...) any)])

(test
 (test-equal (term (range-contracts (((pred string? f) (env))) ()))
             (term ()))
 (test-equal (term (range-contracts ((((pred exact-nonnegative-integer? f) 
                                       (pred string? f) -> 
                                       (pred exact-nonnegative-integer? f)) 
                                      (env))
                                     (((pred boolean? f) 
                                       (pred empty? f) -> 
                                       (pred exact-nonnegative-integer? f)) 
                                      (env)))
                                    ((-- (↓ 0 (env))) (-- (↓ 9 (env))))))
             (term (((pred exact-nonnegative-integer? f) (env))
                    ((pred exact-nonnegative-integer? f) (env)))))
 (test-equal (term (range-contracts ((((pred exact-nonnegative-integer? f) 
                                       -> (λ (x) (pred (λ (y) (@ = x y f)) f))) (env)))
                                    ((-- (↓ 0 (env))))))
             (term (((pred (λ (y) (@ = x y f)) f) 
                     (env (x (-- (↓ 0 (env))))))))))


(define-metafunction λcρ
  env-extend : ρ (X V) ... -> ρ
  [(env-extend ρ (X_2 V_2) ...)
   ,(apply hash-set* (term ρ) 
           (apply append (term ((X_2 V_2) ...))))])
