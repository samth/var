#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta-misc.rkt" "op.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(provide (all-from-out "meta-misc.rkt"))
(test-suite test meta)

(define-metafunction λcρ
  δ : OP V ... -> (A A ...) ;; FIXME: eventually should be (V ...)
  [(δ cons V_0 V_1) ; cons works same for concrete and abstract
   ((-- (cons V_0 V_1)))]  
  [(δ (s-cons X_m X_tag natural) V ...)
   ((-- (struct X_m X_tag V ...)))
   (side-condition (= (length (term (V ...))) (term natural)))]
  [(δ car V) (proj-left V)]
  [(δ cdr V) (proj-right V)]  
  [(δ OP V_1 ... AV V_2 ...)
   (abs-δ OP V_1 ... AV V_2 ...)]  
  [(δ OP V ...) 
   ((plain-δ OP V ...))])
  

(define-metafunction λcρ
  abs-δ : OP V ... AV V ... -> (A ...) ;; FIXME: eventually should be (V ...)
  [(abs-δ OP? AV)
   ((-- (↓ #t (env))))
   (judgment-holds (proves AV OP?))]
  [(abs-δ OP? AV)
   ((-- (↓ #f (env))))
   (judgment-holds (refutes AV OP?))]
  [(abs-δ OP? AV)
   ((-- (↓ #t (env)))
    (-- (↓ #f (env))))]   
  [(abs-δ procedure-arity-includes? AV (-- (clos natural ρ) C ...))
   ((-- (↓ #t (env))))
   (where #t (arity-includes? AV natural))]
  [(abs-δ procedure-arity-includes? V_0 V_1)
   ((-- (↓ #t (env)))
    (-- (↓ #f (env))))]  
  [(abs-δ random V)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))]
  [(abs-δ natural->natural V)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))]  
  [(abs-δ natural-positive->natural V_1 V_2)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))]
  [(abs-δ natural-natural->natural V_1 V_2)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))] 
  [(abs-δ natural*->natural V_1 ...)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))]
  [(abs-δ natural*-natural->natural V_1 ...)
   ((-- ((pred exact-nonnegative-integer? Λ) (env))))]
  [(abs-δ natural-natural-natural*->bool V_1 V_2 V_3 ...)
   ((-- (↓ #t (env)))
    (-- (↓ #f (env))))]    
  [(abs-δ symbol=? V_1 V_2)
   ((-- ((pred boolean? Λ) (env))))]     
  [(abs-δ string-string-string*->bool V_1 V_2 V_3 ...)
   ((-- (↓ #t (env)))
    (-- (↓ #f (env))))]
  ;; FIXME: could discriminate many more things
  [(abs-δ eqv? V_1 V_2)
   ((-- (↓ #t (env)))
    (-- (↓ #f (env))))]
  [(abs-δ not V)
   ((-- (↓ #t (env))))
   (judgment-holds (proves V false?))]
  [(abs-δ not V)
   ((-- (↓ #f (env))))
   (judgment-holds (refutes V false?))]
  [(abs-δ not V)
   ((-- (↓ #t (env)))
    (-- (↓ #f (env))))]  
  
  ;; struct ops
  [(abs-δ (s-pred X_m X_tag) AV)
   ((-- (↓ #t (env))))
   (judgment-holds (proves AV (s-pred X_m X_tag)))]
  [(abs-δ (s-pred X_m X_tag) AV)
   ((-- (↓ #f (env))))
   (judgment-holds (refutes AV (s-pred X_m X_tag)))]  
  [(abs-δ (s-pred X_m X_tag) AV)
   ((-- (↓ #t (env)))
    (-- (↓ #f (env))))
   (judgment-holds (indy AV (s-pred X_m X_tag)))]
     
  [(abs-δ (s-ref X_m X_tag natural) AV)
   (proj-struct AV X_m X_tag natural)
   (where #t (has-struct/c? AV X_m X_tag))]
  
  [(abs-δ (s-ref X_m X_tag natural) AV)
   ((-- ((∧) (env))))
   (judgment-holds (proves AV (s-pred X_m X_tag)))]
  [(abs-δ (s-ref X_m X_tag natural) AV)     ;; FIXME should expressed as a contract
   ((blame FIXMELAB Λ AV (s-ref X_m X_tag natural) AV))
   (judgment-holds (refutes AV (s-pred X_m X_tag)))]
  [(abs-δ (s-ref X_m X_tag natural) AV) ;; FIXME should expressed as a contract
   ((-- ((∧) (env)))
    (blame FIXMELAB Λ AV (s-ref X_m X_tag natural) AV))])
  
(test
 (test-equal (term (δ procedure-arity-includes? (-- ((pred procedure? †) (env))) (-- ((pred exact-nonnegative-integer? †) (env)))))
             (term ((-- (↓ #t (env))) (-- (↓ #f (env))))))
 (test-equal (term (δ procedure-arity-includes? (-- ((pred procedure? †) (env))) (-- (↓ 3 (env)))))
             (term ((-- (↓ #t (env))) (-- (↓ #f (env))))))
 (test-equal (term (δ procedure-arity-includes? (-- ((-> (∧)) (env))) (-- (↓ 0 (env)))))
             (term ((-- (↓ #t (env))))))
 (test-equal (term (δ procedure-arity-includes? (-- ((-> (∧)) (env))) (-- (↓ 1 (env)))))
             (term ((-- (↓ #f (env))))))
 (test-equal (term (δ procedure-arity-includes? (-- (↓ (λ () 0) (env))) (-- ((pred exact-nonnegative-integer? †) (env)))))
             (term ((-- (↓ #t (env))) (-- (↓ #f (env))))))
 (test-equal (term (δ add1 (-- ((pred exact-nonnegative-integer? †) (env)))))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env))))))
 
 (test-equal (term (δ + (-- (↓ 0 (env))) (-- ((pred exact-nonnegative-integer? †) (env)))))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env))))))
 (test-equal (term (δ + (-- ((pred exact-nonnegative-integer? †) (env))) (-- (↓ 0 (env)))))
             (term ((-- ((pred exact-nonnegative-integer? Λ) (env))))))   
 
 (test-equal (term (δ string=? (-- (↓ "" (env))) (-- ((pred string? †) (env)))))
             (term ((-- (↓ #t (env))) (-- (↓ #f (env))))))
 (test-equal (term (δ string=? (-- ((pred string? †) (env))) (-- (↓ "" (env)))))
             (term ((-- (↓ #t (env))) (-- (↓ #f (env))))))
 
 (test-equal (term (δ car (-- ((cons/c (pred string? f) (∧)) (env)))))
             (term ((-- ((pred string? f) (env))))))
 (test-equal (term (δ car (-- ((pred cons? f) (env)))))
             (term ((-- ((∧) (env))))))
 (test-equal (term (δ cdr (-- ((cons/c (∧) (pred string? f)) (env)))))
             (term ((-- ((pred string? f) (env))))))
 (test-equal (term (δ cdr (-- ((pred cons? f) (env)))))
             (term ((-- ((∧) (env))))))

 (test-equal (term (abs-δ (s-pred p posn) (-- ((pred (posn? ^ g p) f) (env)))))
             (term ((-- (↓ #t (env))))))
 ;; FIXME fails (returns both #t, #f), but want just #f.
 (test-equal (term (abs-δ (s-pred p posn) (-- ((pred string? f) (env)))))
             (term ((-- (↓ #f (env))))))
 (test-equal (term (abs-δ (s-pred p posn) (-- ((∧) (env)))))
             (term ((-- (↓ #t (env)))
                    (-- (↓ #f (env)))))) 
 
 (test-equal (term (abs-δ (s-ref p posn 0) (-- ((pred (posn? ^ g p) f) (env)))))
             (term ((-- ((∧) (env)))))))


(define-metafunction λcρ
  plain-δ : OP V ... -> V
  [(plain-δ procedure? PROC)
   (-- (↓ #t (env)))]
  [(plain-δ procedure? V)
   (-- (↓ #f (env)))]
  [(plain-δ string? (-- (clos string ρ))) 
   (-- (↓ #t (env)))]
  [(plain-δ string? V) 
   (-- (↓ #f (env)))]
  [(plain-δ char? (-- (clos character ρ))) 
   (-- (↓ #t (env)))]
  [(plain-δ char? V) 
   (-- (↓ #f (env)))]  
  [(plain-δ boolean? (-- (clos boolean ρ) C ...)) 
   (-- (↓ #t (env)))]
  [(plain-δ boolean? V) 
   (-- (↓ #f (env)))]
  [(plain-δ zero? (-- (clos 0 ρ) C ...)) 
   (-- (↓ #t (env)))]
  [(plain-δ zero? (-- (clos natural ρ) C ...)) 
   (-- (↓ #f (env)))]  
  [(plain-δ empty? (-- (clos empty ρ) C ...))
   (-- (↓ #t (env)))]
  [(plain-δ empty? V)
   (-- (↓ #f (env)))]
  [(plain-δ cons? (-- (cons V_0 V_1) C ...))
   (-- (↓ #t (env)))]    
  [(plain-δ cons? V)
   (-- (↓ #f (env)))]  
  [(plain-δ exact-nonnegative-integer? (-- (clos natural ρ) C ...))
   (-- (↓ #t (env)))]
  [(plain-δ exact-nonnegative-integer? V) 
   (-- (↓ #f (env)))]  
  [(plain-δ false? (-- (clos #f ρ) C ...)) 
   (-- (↓ #t (env)))]
  [(plain-δ false? V) 
   (-- (↓ #f (env)))]
  [(plain-δ symbol? (-- (clos 'variable ρ) C ...))
   (-- (↓ #t (env)))]
  [(plain-δ symbol? (-- (clos 'variable ρ) C ...)) 
   (-- (↓ #f (env)))]
  [(plain-δ not (-- (clos #f ρ) C ...))
   (-- (↓ #t (env)))]
  [(plain-δ not V)
   (-- (↓ #f (env)))]
  ;; Interpreted different than Racket's `sub1', `random', etc.
  [(plain-δ sub1 (-- (clos natural ρ) C ...))
   (-- (↓ ,(max 0 (sub1 (term natural))) (env)))]  
  [(plain-δ natural->natural (-- (clos natural ρ) C ...))
   (meta-apply natural->natural natural)]  
  [(plain-δ procedure-arity-includes? V (-- (clos natural ρ) C ...))
   (-- (↓ (arity-includes? V natural) (env)))]
  [(plain-δ natural-positive->natural
            (-- (clos natural_1 ρ_1) C_1 ...)
            (-- (clos natural_2 ρ_2) C_2 ...))
   (meta-apply natural-positive->natural natural_1 natural_2)]
  [(plain-δ natural*->natural V ...)
   (-- (↓ ,(apply (lift (term natural*->natural)) (term (natural ...))) (env)))
   (where ((-- (clos natural ρ) C ...) ...)
          (V ...))]
  [(plain-δ natural-natural*->natural V ...)
   (-- (↓ ,(apply (lift (term natural-natural*->natural)) (term (natural ...))) (env)))
   (where ((-- (clos natural ρ) C ...) ...)
          (V ...))]
  [(plain-δ natural-natural->natural
            (-- (clos natural_1 ρ_1) C_1 ...)
            (-- (clos natural_2 ρ_2) C_2 ...))
   (meta-apply natural-natural->natural natural_1 natural_2)]  
  [(plain-δ natural-natural-natural*->bool
            (-- (clos natural ρ) C ...)
            ...)
   (meta-apply natural-natural-natural*->bool natural ...)]
  [(plain-δ string-string-string*->bool (-- (clos string ρ) C ...) ...)            
   (meta-apply string-string-string*->bool string ...)]
  [(plain-δ char-char-char*->bool (-- (clos character ρ) C ...) ...)
   (meta-apply char-char-char*->bool character ...)]
  [(plain-δ symbol=?
            (-- (clos 'variable_1 ρ_1) C_1 ...)
            (-- (clos 'variable_2 ρ_2) C_2 ...))
   (meta-apply symbol=? variable_1 variable_2)]
  ;; Structs
  [(plain-δ (s-pred X_m X_tag) (-- (struct X_m X_tag V ...) C ...))
   (-- (↓ #t (env)))]
  [(plain-δ (s-pred X_m X_tag) V)
   (-- (↓ #f (env)))]
  [(plain-δ (s-ref X_m X_tag natural) (-- (struct X_m X_tag V ...) C ...))
   V_i
   (where V_i ,(list-ref (term (V ...)) (term natural)))]
  [(plain-δ (s-pred X_m X_tag) (-- (struct X_m X_tag V ...) C ...))
   (-- (↓ #t (env)))]
  [(plain-δ (s-pred X_m X_tag) V)
   (-- (↓ #f (env)))]
  ;; eqv?
  [(plain-δ eqv? PROC_1 PROC_2) 
   (-- (↓ #f (env)))]
  [(plain-δ eqv? 
            (-- (clos 'variable_1 ρ_1) C_1 ...)
            (-- (clos 'variable_2 ρ_2) C_2 ...))
   (-- (↓ #t (env)))
   (side-condition (eqv? (term variable_1) (term variable_2)))]
  [(plain-δ eqv? 
            (-- (clos VAL_1 ρ_1) C_1 ...)
            (-- (clos VAL_2 ρ_2) C_2 ...))
   (-- (↓ #t (env)))
   (side-condition (eqv? (term VAL_1) (term VAL_2)))]
  [(plain-δ eqv? V_1 V_2)
   (-- (↓ #f (env)))])

(test 
 (test-equal (term (δ cons (-- (↓ 0 (env))) (-- (↓ 1 (env)))))
             (term ((-- (cons (-- (↓ 0 (env))) (-- (↓ 1 (env))))))))
 (test-equal (term (plain-δ add1 (-- (↓ 5 (env)))))
             (term (-- (↓ 6 (env)))))
 (test-equal (term (plain-δ sub1 (-- (↓ 5 (env)))))
             (term (-- (↓ 4 (env)))))
 (test-equal (term (plain-δ sub1 (-- (↓ 0 (env)))))
             (term (-- (↓ 0 (env))))) 
 (test-equal (term (plain-δ +
                            (-- (↓ 3 (env)))
                            (-- (↓ 3 (env)))))
             (term (-- (↓ 6 (env)))))
 (test-equal (term (plain-δ string=? 
                            (-- (↓ "Hi" (env)))
                            (-- (↓ "Hi" (env)))))
             (term (-- (↓ #t (env)))))
 (test-equal (term (plain-δ empty? (-- (↓ empty #hash()))))
             (term (-- (↓ #t (env)))))
 (test-equal (term (plain-δ =
                            (-- (↓ 3 (env)))
                            (-- (↓ 3 (env)))))
             (term (-- (↓ #t (env)))))
 
 (test-equal (term (plain-δ (s-pred p posn) (-- (struct p posn))))
             (term (-- (↓ #t (env)))))
 (test-equal (term (plain-δ (s-pred p posn) (-- (struct p blah))))
             (term (-- (↓ #f (env)))))
 (test-equal (term (plain-δ (s-pred p posn) (-- (↓ 0 (env)))))
             (term (-- (↓ #f (env)))))
 (test-equal (term (δ (s-cons p posn 0)))
             (term ((-- (struct p posn)))))
 (test-equal (term (δ (s-cons p posn 2) (-- (↓ 0 (env))) (-- (↓ 1 (env)))))
             (term ((-- (struct p posn (-- (↓ 0 (env))) (-- (↓ 1 (env))))))))
 (test-equal (term (plain-δ (s-ref p posn 0) (-- (struct p posn (-- (↓ 0 (env))) (-- (↓ 5 (env)))))))
             (term (-- (↓ 0 (env)))))
 (test-equal (term (plain-δ (s-ref p posn 1) (-- (struct p posn (-- (↓ 0 (env))) (-- (↓ 5 (env)))))))
             (term (-- (↓ 5 (env)))))
 (test-equal (term (plain-δ eqv? (-- (↓ 0 (env))) (-- (↓ 0 (env)))))
             (term (-- (↓ #t (env)))))
 (test-equal (term (plain-δ eqv? (-- (↓ (λ (x) x) (env))) (-- (↓ (λ (x) x) (env)))))
             (term (-- (↓ #f (env)))))
 (test-equal (term (plain-δ eqv? (-- (↓ 'x (env))) (-- (↓ 'x (env)))))
             (term (-- (↓ #t (env)))))
 (test-equal (term (plain-δ eqv? (-- (↓ 'x (env))) (-- (↓ 'y (env)))))
             (term (-- (↓ #f (env)))))
 )


(define-metafunction λcρ
  meta-apply : OP any ... -> D
  [(meta-apply OP any ...)
   (-- (↓ ,(apply (lift (term OP)) (term (any ...))) (env)))])

(define (lift f)
  (define-syntax reflect
    (syntax-rules ()
      [(reflect id ...)
       (case f 
         [(id) id] ...
         [else (error 'lift "unknown procedure: ~a" f)])]))
  (reflect add1 random + * expt 
           quotient remainder modulo 
           = < <= > >=        
           symbol=?
           char=? char<? char<=? char>=? char>?
           string=? string<? string>? string<=? string>=?
           string-ci=? string-ci<? string-ci>? string-ci<=? string-ci>=?))

(define-judgment-form λcρ
  #:mode (contract-in I I)
  #:contract (contract-in C V)
  [(contract-in C (-- any ... C_0 C_1 ...))
   (where #t (≡C C_0 C))]
  [(contract-in C (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V))
   (contract-in C V)]
  [(contract-in ((atom/c ATOMLIT LAB) ρ) (-- (clos ATOMLIT ρ) C ...))]
  [(contract-in ((pred OP LAB) ρ) V)
   (proves V OP)]    
  [(contract-in ((and/c CON_1 CON_2) ρ) V)
   (contract-in (CON_1 ρ) V)
   (contract-in (CON_2 ρ) V)]
  [(contract-in ((or/c CON_1 CON_2) ρ) V)
   (contract-in (CON_1 ρ) V)]
  [(contract-in ((or/c CON_1 CON_2) ρ) V)
   (contract-in (CON_2 ρ) V)]
  [(contract-in ((cons/c CON_1 CON_2) ρ) (-- (cons V_1 V_2) C ...))
   (contract-in (CON_1 ρ) V_1)
   (contract-in (CON_2 ρ) V_2)]
  [(contract-in ((not/c CON_1) ρ) V)
   (contract-not-in (CON_1 ρ) V)]
  [(contract-in ((cons/c CON_1 CON_2) ρ) AV)
   (proves AV cons?)
   (where (V_left ...) (proj-left AV))
   (where (V_right ...) (proj-right AV))
   (contract-in (CON_1 ρ) V_left) 
   ...
   (contract-in (CON_2 ρ) V_right)
   ...
   ])  

(test
 (test-equal (judgment-holds (contract-in ((pred procedure? †) (env))
                                          (-- (↓ (λ (x) x) (env)))))
             #t)
 (test-equal (judgment-holds (contract-in ((pred zero? †) (env))
                                          (-- (↓ 0 (env))))) 
             #t)
 (test-equal (judgment-holds (contract-in ((pred procedure? †) (env))
                                          ((--> (pred (λ (x) x) †)) (env) <= f g (-- (↓ 0 (env))) f (-- (↓ (λ (x) x) (env))))))
             #t)
 (test-equal (judgment-holds (contract-in ((pred (prime? ^ f g) †) (env))
                                          (-- (↓ "a" (env)) ((pred (prime? ^ f g) †) (env)))))
             #t)
 (test-equal (judgment-holds (contract-in ((pred (prime? ^ g f) †) (env))
                                          (-- (↓ "a" (env)) ((pred (prime? ^ h f) †) (env)))))
             #t)
 (test-equal (judgment-holds (contract-in ((and/c (pred zero? †) (pred exact-nonnegative-integer? †)) (env))
                                          (-- (↓ 0 (env)))))
             #t)
 (test-equal (judgment-holds (contract-in ((and/c (pred zero? †) (pred exact-nonnegative-integer? †)) (env))
                                          (-- (↓ 1 (env)))))
             #f)
 (test-equal (judgment-holds (contract-in ((or/c (pred zero? †) (pred exact-nonnegative-integer? †)) (env))
                                          (-- (↓ 1 (env)))))
             #t)
 (test-equal (judgment-holds (contract-in ((cons/c (pred zero? †) (pred string? †)) (env))
                                          (-- (cons (-- (↓ 0 (env))) (-- (↓ "s" (env)))))))
             #t)
 (test-equal (judgment-holds (contract-in ((cons/c (pred zero? †) (pred string? †)) (env))
                                          (-- (cons (-- (↓ 0 (env))) (-- (↓ 2 (env)))))))
             #f)
 (test-equal (judgment-holds (contract-in ((cons/c (pred zero? †) (pred symbol? †)) (env))
                                          (-- ((cons/c (atom/c 0 f) (atom/c 's f)) (env)))))
             #t)
 
 (test-equal (judgment-holds (contract-in ((not/c (pred cons? †)) (env))
                                          (-- (↓ 1 (env)))))
             #t)
 
 (test-equal (judgment-holds (contract-in ((not/c (pred cons? †)) (env))
                                          (-- (cons (-- (↓ 0 (env))) (-- (↓ 2 (env)))))))
             #f)
 ;; We should really get true here, but it requires more work.
 ;; FIXME known to fail; requires caching
 (test-equal (judgment-holds (contract-in ((rec/c x 
                                                  (or/c (pred empty? †)
                                                        (cons/c (pred zero? †) x))) 
                                           (env))
                                          (-- (cons (-- (↓ 0 (env)))
                                                    (-- (↓ empty (env)))))))
             #t))

;; Does this value *definitely* fail this contract?
(define-judgment-form λcρ
  #:mode (contract-not-in I I)
  #:contract (contract-not-in C V)
  [(contract-not-in C V)
   (contract-not-in/cache C V () #t)])

(define-judgment-form λcρ
  #:mode (contract-not-in/cache I I I O)
  #:contract (contract-not-in/cache C V ((C V) ...) any_bool)
  [(contract-not-in/cache C V ((C_0 V_0) ... (C V) (C_1 V_1) ...) #f)] ;; FIXME -- use ≡C 
  [(contract-not-in/cache C (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) any #t)
   (contract-not-in/cache C V any #t)]
  [(contract-not-in/cache ((atom/c ATOMLIT_!_1 LAB) ρ_1) (-- (clos ATOMLIT_!_1 ρ_2) C_1 ...) any #t)]
  [(contract-not-in/cache ((pred OP LAB) ρ) V any #t)
   (refutes V OP)]
  
  [(contract-not-in/cache ((struct/c any_1 ...) ρ) (-- C ... ((pred OP? LAB) ρ_1) C_1 ...) any #f)]
   
  ;; FIXME
  ;[(contract-not-in/cache ((struct/c X_m X_tag any_1 ...) ρ) (-- PREVAL C_1 ...) any #t
  ; #t
  ; (side-condition (not (redex-match λcρ (struct X_m X_tag any_2 ...) (term PREVAL)))))]
  
  [(contract-not-in/cache ((cons/c CON_1 CON_2) ρ) V ((C_3 V_3) ...) #t)
   (refutes V cons?)]
  [(contract-not-in/cache ((cons/c CON_1 CON_2) ρ) V ((C_3 V_3) ...) #t)   
   (where (V_car ...) (proj-left V))
   (contract-not-in/cache (CON_1 ρ) V_car ((((cons/c CON_1 CON_2) ρ) V) (C_3 V_3) ...) #t)
   ...]
  [(contract-not-in/cache ((cons/c CON_1 CON_2) ρ) V ((C_3 V_3) ...) #t)
   (where (V_cdr ...) (proj-right V))
   (contract-not-in/cache (CON_2 ρ) V_cdr ((((cons/c CON_1 CON_2) ρ) V) (C_3 V_3) ...) #t)
   ...]
  [(contract-not-in/cache ((and/c CON_1 CON_2) ρ) V ((C_3 V_3) ...) #t)
   (contract-not-in/cache (CON_1 ρ) V ((((and/c CON_1 CON_2) ρ) V) (C_3 V_3) ...) #t)]
  [(contract-not-in/cache ((and/c CON_1 CON_2) ρ) V ((C_3 V_3) ...) #t)
   (contract-not-in/cache (CON_2 ρ) V ((((and/c CON_1 CON_2) ρ) V) (C_3 V_3) ...) #t)]  
  [(contract-not-in/cache ((or/c CON_1 CON_2) ρ) V ((C_3 V_3) ...) #t)
   (contract-not-in/cache (CON_1 ρ) V ((((or/c CON_1 CON_2) ρ) V) (C_3 V_3) ...) #t)
   (contract-not-in/cache (CON_2 ρ) V ((((or/c CON_1 CON_2) ρ) V) (C_3 V_3) ...) #t)]  
  [(contract-not-in/cache ((not/c CON_1) ρ) V ((C_3 V_3) ...) #t)
   (contract-in (CON_1 ρ) V)] ;; FIXME -- use contract-not-in/cache when it exists 
  [(contract-not-in/cache ((rec/c X CON) ρ) V ((C_3 V_3) ...) #t)
   (contract-not-in/cache ((unroll (rec/c X CON)) ρ) V ((((rec/c X CON) ρ) V) (C_3 V_3) ...) #t)])
  
 
 
(test
 (test-equal (judgment-holds (contract-not-in ((pred string? †) (env)) 
                                              (-- (↓ 3 (env)))))
             #t)
 (test-equal (judgment-holds (contract-not-in ((pred string? †) (env)) 
                                              ((--> (pred string? †)) (env) <= f g (-- (↓ 0 (env))) f (-- (↓ (λ (x) x) (env))))))
             #t)
 (test-equal (judgment-holds (contract-not-in ((cons/c (pred string? †) (pred zero? †)) (env))
                                              (-- (cons (-- (↓ "" (env))) (-- (↓ 0 (env)))))))
             #f)
 (test-equal (judgment-holds (contract-not-in ((cons/c (pred string? †) (pred zero? †)) (env))
                                              (-- (cons (-- (↓ "" (env))) (-- (↓ 2 (env)))))))
             #t)
 (test-equal (judgment-holds (contract-not-in ((rec/c x (or/c (pred empty? †) (cons/c (pred string? †) x))) (env))
                                              (-- (↓ (λ (x) x) (env)))))
             #t))

  #|
  [(contract-not-in/cache (C_1 ... -> any) V any_1)
   #t
   (where #t (refutes V procedure?))]
    |#


(define-metafunction λcρ
  indy-hack : V OP -> #t or #f
  [(indy-hack V OP) #t
   (side-condition (not (judgment-holds (proves V OP))))
   (side-condition (not (judgment-holds (refutes V OP))))])

(define-judgment-form λcρ
  #:mode (indy I I)
  #:contract (indy V OP)
  [(indy V OP)
   (where #t (indy-hack V OP))
   ;; This doesn't work:
   #;(where #f (judgment-holds (proves V OP)))
   #;(where #f (judgment-holds (refutes V OP)))])

;; Does OP hold on all values abstracted by V
;; [Gives an approximate answer: #f means "failed to prove"]
(define-judgment-form λcρ
  #:mode (proves I I)
  #:contract (proves V OP)
  [(proves (-- PREVAL C ...) OP)
   (where TRUE (plain-δ OP (-- PREVAL C ...)))]
  [(proves (-- C_0 ... C C_1 ...) OP)
   (proves-con C OP)]
  [(proves (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) OP)
   (proves V OP)])

(test
 (test-equal (judgment-holds (proves (-- (↓ "Hi" (env))) string?)) #t)
 (test-equal (judgment-holds (proves ((--> (pred (λ (x) #t) f)) (env) <= f g 
                                                                (-- (↓ 0 (env))) h 
                                                                (-- (↓ (λ (x) x) (env))))
                                     procedure?))
             #t) 
 
 (test-equal (judgment-holds (proves (-- ((pred procedure? Λ) (env)))
                                     procedure?))
             #t)
 
 (test-equal (judgment-holds (proves ((--> (pred (λ (x) #t) f)) 
                                      (env) <= f g 
                                      (-- (↓ 0 (env))) h 
                                      (-- ((pred procedure? Λ) (env))))
                                     procedure?))
             #t)
 (test-equal (judgment-holds (proves (-- ((rec/c X (pred cons? m)) (env))) cons?))
             #t))
                                                           

;; side-condition
(define-metafunction λcρ
  meq? : any any -> #t or #f
  [(meq? any_x any_y) ,(eq? (term any_x) (term any_y))])
  
;; Does (negate o?) hold on all values abstracted by AV
(define-judgment-form λcρ
  #:mode (refutes I I)
  #:contract (refutes V OP)
  [(refutes (-- C_0 ... C C_1 ...) OP) 
   (refutes-con C OP)]  
  [(refutes (-- PREVAL C ...) OP)  
   (where FALSE (plain-δ OP (-- PREVAL C ...)))]
  [(refutes (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 any_1) OP)
   (where #f (meq? OP procedure?))]   
  [(refutes (BARROW ρ <= LAB_0 LAB_1 V_b LAB_2 V) OP)
   (refutes V OP)])

(test
 (test-equal (judgment-holds (refutes (-- (↓ 0 (env))) empty?)) #t)
 (test-equal (judgment-holds (refutes (-- (cons (-- (↓ 0 (env))) (-- (↓ 1 (env))))) cons?)) #f)
 (test-equal (judgment-holds (refutes (-- (cons (-- (↓ 0 (env))) (-- (↓ 1 (env))))) string?)) #t)
 (test-equal (judgment-holds (refutes ((--> (pred string? †)) (env) <= f g (-- (↓ 0 (env))) f (-- (↓ (λ () 1) (env)))) string?))
             #t)
 (test-equal (judgment-holds (refutes ((--> (pred string? †)) (env) <= f g (-- (↓ 0 (env))) f (-- (↓ (λ () 1) (env)))) procedure?))
             #f)
                   
 #;
 (test-equal (term (refutes (-- (cons/c (pred exact-nonnegative-integer? p) (pred exact-nonnegative-integer? p))) cons?)) #f)
 )

;; Does satisfying C imply o?
(define-judgment-form λcρ
  #:mode (proves-con I I)
  #:contract (proves-con C OP)
  [(proves-con ((pred OP_0 LAB) ρ) OP_1)
   (proves-pred OP_0 OP_1)]
  [(proves-con ((struct/c X_m X_tag any_s ...) ρ) (s-pred X_m X_tag))]  
  [(proves-con ((pred (X_spred ^ LAB_0 LAB_p) LAB) ρ) (s-pred LAB_p X_tag))  
   (where X_spred (tag->pred X_tag))]
  [(proves-con ((atom/c ATOMLIT LAB) ρ) OP)   
   (where TRUE (plain-δ OP (-- (↓ ATOMLIT (env)))))]
  [(proves-con ((or/c CON_0 CON_1) ρ) OP)
   (proves-con (CON_0 ρ) OP)
   (proves-con (CON_1 ρ) OP)]
  [(proves-con ((and/c CON_0 CON_1) ρ) OP)
   (proves-con (CON_0 ρ) OP)]
  [(proves-con ((and/c CON_0 CON_1) ρ) OP)
   (proves-con (CON_1 ρ) OP)]
  ; This isn't right at all -- pretty sure (not/c C) proves no OP.
  ;[(proves-con ((not/c CON_0) ρ) OP)
  ; (refutes-con (CON_0 ρ) OP)]
  [(proves-con ((cons/c CON_0 CON_1) ρ) cons?)]
  [(proves-con ((CON_0 ... -> any) ρ) procedure?)]
  [(proves-con ((rec/c X CON) ρ) OP)
   (proves-con ((unroll (rec/c X CON)) ρ) OP)])

(test
 (test-equal (judgment-holds (proves-con ((pred procedure? Λ) (env)) procedure?)) #t)
 (test-equal (judgment-holds (proves-con ((pred procedure? Λ) (env)) string?)) #f)
 (test-equal (judgment-holds (proves-con ((pred false? †) (env)) boolean?)) #t)
 (test-equal (judgment-holds (proves-con ((cons/c (pred string? †) (pred boolean? †)) (env))
                                         cons?))
             #t)
 (test-equal (judgment-holds (proves-con ((-> (pred string? †)) (env)) procedure?)) #t)
 (test-equal (judgment-holds (proves-con ((-> (pred string? †)) (env)) string?)) #f)
 (test-equal (judgment-holds (proves-con ((and/c (pred boolean? †) (pred false? †)) (env)) false?)) #t)
 (test-equal (judgment-holds (proves-con ((or/c (pred boolean? †) (pred false? †)) (env)) false?)) #f)
 (test-equal (judgment-holds (proves-con ((or/c (pred false? †) (pred boolean? †)) (env)) false?)) #f)
 (test-equal (judgment-holds (proves-con ((not/c (atom/c 's f)) (env)) symbol?)) #f)
 (test-equal (judgment-holds (proves-con ((not/c (pred cons? f)) (env)) symbol?)) #f))

(define-judgment-form λcρ
  #:mode (proves-pred I I)
  #:contract (proves-pred OP OP)
  [(proves-pred OP OP)]
  [(proves-pred zero? exact-nonnegative-integer?)]
  [(proves-pred false? boolean?)])

;; Does satisfying C imply (negate o?)
(define-judgment-form λcρ
  #:mode (refutes-con I I)
  #:contract (refutes-con C OP)      
  [(refutes-con ((CON_0 ... -> any) ρ) OP)
   (where #f (meq? OP procedure?))]
  
  ;; structs are disjoint
  [(refutes-con ((struct/c X_tag X_m any_s ...) ρ) (s-pred X_tag2 X_m2))
   (where #f (meq? X_tag X_tag2))]
  [(refutes-con ((struct/c X_tag X_m any_s ...) ρ) (s-pred X_tag2 X_m2))
   (where #f (meq? X_m X_m2))]
  ;; structs are not op? for any op?
  [(refutes-con ((struct/c X_tag X_m any_s ...) ρ) OP?)]
  [(refutes-con (pred OP? LAB) (s-pred any ...))]
  
  [(refutes-con ((pred OP_0 LAB) ρ) OP_1) 
   (refutes-pred OP_0 OP_1)]
  [(refutes-con ((atom/c ATOMLIT LAB) ρ) OP)   
   (where FALSE (plain-δ OP (-- (↓ ATOMLIT (env)))))]
  [(refutes-con ((or/c CON_0 CON_1) ρ) OP)
   (refutes-con (CON_0 ρ) OP)
   (refutes-con (CON_1 ρ) OP)]
  [(refutes-con ((and/c CON_0 CON_1) ρ) OP)
   (refutes-con (CON_0 ρ) OP)]
  [(refutes-con ((and/c CON_0 CON_1) ρ) OP)
   (refutes-con (CON_1 ρ) OP)]
  ; This isn't right either: let CON = zero?, OP = nat?
  ;[(refutes-con ((not/c CON) ρ) OP)
  ; (proves-con (CON ρ) OP)]
  [(refutes-con ((not/c (pred OP LAB)) ρ) OP)] ; As good as I can do.
  [(refutes-con ((cons/c CON_0 CON_1) ρ) OP) 
   (where #f (meq? OP cons?))]
  
  [(refutes-con ((rec/c X CON) ρ) OP) 
   ;; Productive implies you'll never get a loop
   (refutes-con ((unroll (rec/c X CON)) ρ) OP)])

(test 
 (test-equal (judgment-holds (refutes-con ((-> (∧)) (env)) procedure?)) #f)
 (test-equal (judgment-holds (refutes-con ((-> (∧)) (env)) cons?)) #t) 
 (test-equal (judgment-holds (refutes-con ((struct/c p posn) (env)) (s-pred p pair))) #t)
 (test-equal (judgment-holds (refutes-con ((struct/c p posn) (env)) (s-pred p posn))) #f)
 (test-equal (judgment-holds (refutes-con ((struct/c p posn) (env)) (s-pred m posn))) #t)
 (test-equal (judgment-holds (refutes-con ((or/c (atom/c 'x f) (atom/c 'y f)) (env)) cons?)) #t)
 (test-equal (judgment-holds (refutes-con ((or/c (atom/c 'x f) (atom/c 'y f)) (env)) symbol?)) #f)
 (test-equal (judgment-holds (refutes-con ((and/c (pred symbol? f) (atom/c 'y f)) (env)) symbol?)) #f)
 (test-equal (judgment-holds (refutes-con ((and/c (pred symbol? f) (atom/c 'y f)) (env)) cons?)) #t)
 (test-equal (judgment-holds (refutes-con ((not/c (pred symbol? f)) (env)) symbol?)) #t)
 (test-equal (judgment-holds (refutes-con ((not/c (pred zero? f)) (env)) exact-nonnegative-integer?)) #f)
 (test-equal (judgment-holds (refutes-con ((atom/c 'x f) (env)) cons?)) #t)
 (test-equal (judgment-holds (refutes-con ((atom/c 'x f) (env)) symbol?)) #f)
 (test-equal (judgment-holds (refutes-con ((cons/c (∧) (∧)) (env)) symbol?)) #t)
 (test-equal (judgment-holds (refutes-con ((cons/c (∧) (∧)) (env)) cons?)) #f)
 (test-equal (judgment-holds (refutes-con ((rec/c X (pred string? f)) (env)) symbol?)) #t)
 (test-equal (judgment-holds (refutes-con ((pred string? f) (env)) exact-nonnegative-integer?)) #t))
 
(define-judgment-form λcρ
  #:mode (refutes-pred I I)
  #:contract (refutes-pred OP OP)  
  [(refutes-pred empty? OP) 
   (where #f (meq? empty? OP))]
  [(refutes-pred cons? OP)
   (where #f (meq? cons? OP))]
  [(refutes-pred exact-nonnegative-integer? OP)
   (where #f (meq? exact-nonnegative-integer? OP))
   (where #f (meq? zero? OP))]  
  [(refutes-pred zero? OP)
   (where #f (meq? exact-nonnegative-integer? OP))
   (where #f (meq? zero? OP))]  
  [(refutes-pred procedure? OP) 
   (where #f (meq? procedure? OP))]  
  [(refutes-pred boolean? OP) 
   (where #f (meq? boolean? OP))
   (where #f (meq? false? OP))]    
  [(refutes-pred string? OP) 
   (where #f (meq? string? OP))]
  [(refutes-pred false? OP) 
   (where #f (meq? false? OP))
   (where #f (meq? boolean? OP))])
     
(define-metafunction λcρ
  has-struct/c? : AV X X -> #t or #f
  [(has-struct/c? (-- C_1 ... ((struct/c X_m X_tag CON ...) ρ) C_2 ...) X_m X_tag)
   #t]
  [(has-struct/c? (-- C ...) X_m X_tag) #f])


(define-metafunction λcρ
  push-close : VAL -> V
  [(push-close (cons VAL_1 VAL_2))
   (-- (cons (push-close VAL_1)
             (push-close VAL_2)))]
  [(push-close VAL)
   (-- (clos VAL (env)))])

(define-metafunction λcρ
  struct-op/contract : OP LAB -> V
  [(struct-op/contract (s-pred X_mod X_tag) LAB_use)
   (((∧) --> (pred boolean? Λ)) 
    (env) <= Λ LAB_use
    (-- (clos (s-pred X_mod X_tag) (env)))
    Λ
    (-- (clos (s-pred X_mod X_tag) (env))))]
  [(struct-op/contract (s-cons X_mod X_tag natural) LAB_use)
   ((,@(build-list (term natural)
                   (λ (_) (term (∧))))
     --> (pred ((tag->pred X_tag) ^ LAB_use X_mod) Λ))
    (env) <= Λ LAB_use
    (-- (clos (s-cons X_mod X_tag natural) (env)))
    Λ
    (-- (clos (s-cons X_mod X_tag natural) (env))))]                      
  [(struct-op/contract (s-ref X_mod X_tag natural) LAB_use) 
   (((pred ((tag->pred X_tag) ^ LAB_use X_mod) Λ) --> (∧))
    (env) <= Λ LAB_use
    (-- (clos (s-ref X_mod X_tag natural) (env)))
    Λ
    (-- (clos (s-ref X_mod X_tag natural) (env))))])

;; valuename x modname x modules -> value
(define-metafunction λcρ
  lookup-modref/val : X LAB X (MOD ...) -> V or •
  [(lookup-modref/val X_name LAB_use X_mod
                      (MOD ... 
                       ;; FIXME should make sure it's provided.
                       (module X_mod LANG REQ STRUCT ... DEF ... (define X_name •) DEF_1 ... any_p) 
                       MOD_1 ...))
   •]
  [(lookup-modref/val X_name LAB_use X_mod
                      (MOD ... 
                       ;; FIXME should make sure it's provided.
                       (module X_mod LANG REQ STRUCT ... DEF ... (define X_name VAL) DEF_1 ... any_p) 
                       MOD_1 ...))
   (push-close VAL)]
  [(lookup-modref/val X_name LAB_use X_mod (MOD ...))
   (struct-op/contract OP LAB_use)   
   (where OP (struct-cons? X_mod X_name (struct-env (MOD ...))))]
  [(lookup-modref/val X_name LAB_use X_mod (MOD ...))
   (struct-op/contract OP LAB_use)
   (where OP (struct-ref? X_mod X_name (struct-env (MOD ...))))]
  [(lookup-modref/val X_name LAB_use X_mod (MOD ...))
   (struct-op/contract OP LAB_use)
   (where OP (struct-pred? X_mod X_name (struct-env (MOD ...))))]
  [(lookup-modref/val X_name LAB_use X_mod any)
   (-- (↓ ,(format "unbound module variable ~a from ~a in ~a" (term X_name) (term X_mod) (term LAB_use)) (env)))])
          
;; valuename x modulename x modules -> contract
(define-metafunction λc-user
  lookup-modref/con : X LAB X (MOD ...) -> CON
  [(lookup-modref/con X_name LAB_use X_mod
                      (MOD ... 
                       (module X_mod LANG REQ STRUCT ... DEF ... 
                         (provide/contract any_1 ... [X_name CON] any_2 ...))
                       MOD_1 ...))
   CON] 
  [(lookup-modref/con X_name LAB_use X_mod any)
   (pred (λ (x) ,(format "contract for unbound module variable ~a from ~a in ~a" (term X_name) (term X_mod) (term LAB_use))) ★)])
   
(test
 (define Ms 
   (term [(module m racket (require) (define f 1) (provide/contract [f (pred string? m)]))]))
 (test-equal (term (lookup-modref/val f h m ,Ms)) (term (-- (↓ 1 (env)))))
 (test-equal (term (lookup-modref/val g h m ,Ms)) (term (-- (↓ "unbound module variable g from m in h" (env)))))
 (test-equal (term (lookup-modref/con f h m ,Ms)) (term (pred string? m)))
 (test-equal (term (lookup-modref/con g h m ,Ms)) 
             (term (pred (λ (x) "contract for unbound module variable g from m in h") ★))))
 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; structure definitions

(define-metafunction λcρ
  struct-cons? : X X STRUCTENV -> OP or #f
  [(struct-cons? X_def X_cons (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc ...)) any_3 ...) any_1 ...))
   (s-cons X_def X_tag ,(length (term (X_acc ...))))]
  [(struct-cons? X_def X STRUCTENV) #f])

(define-metafunction λcρ
  struct-ref? : X X STRUCTENV -> OP or #f
  [(struct-ref? X_def X_acc (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X ... X_acc X_1 ...)) any_3 ...) any_1 ...))
   (s-ref X_def X_tag ,(length (term (X ...))))]
  [(struct-ref? X_def X STRUCTENV) #f])

(define-metafunction λcρ
  struct-pred? : X X STRUCTENV -> OP or #f
  [(struct-pred? X_def X_pred (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc ...)) any_3 ...) any_1 ...))
   (s-pred X_def X_tag)]
  [(struct-pred? X X_def STRUCTENV) #f])

(define-metafunction λcρ
  struct-env : (MOD ...) -> STRUCTENV
  [(struct-env ((module X_m LANG REQ STRUCT ... DEF ... PROV) ...))
   ((X_m (struct-names STRUCT) ...) ...)])
 
(define-metafunction λcρ
  struct-names : STRUCT -> (X X X (X ...))
  [(struct-names (struct X_tag (X_fld ...)))
   (X_tag (tag->cons X_tag) (tag->pred X_tag) ((fld->acc X_tag X_fld) ...))])

;; Change this if you want constructors and tags to be different.
(define-metafunction λcρ
  tag->cons : X -> X
  [(tag->cons X) X])
(define-metafunction λcρ
  tag->pred : X -> X
  [(tag->pred X) ,(string->symbol (format "~a?" (term X)))])
(define-metafunction λcρ
  fld->acc : X X -> X
  [(fld->acc X_tag X_fld) ,(string->symbol (format "~a-~a" (term X_tag) (term X_fld)))])
        
        
(test
 (test-equal (term (tag->cons posn)) (term posn))
 (test-equal (term (tag->pred posn)) (term posn?))
 (test-equal (term (fld->acc posn x)) (term posn-x))
 (test-equal (term (fld->acc posn y)) (term posn-y))
 
 (test-equal (term (struct-names (struct posn (x y))))                                 
             (term (posn posn posn? (posn-x posn-y))))
 
 (test-equal (term (struct-env [(module p racket
                                  (require)
                                  (struct posn (x y))
                                  (provide/contract))]))
             (term ((p (posn posn posn? (posn-x posn-y)))))))

;; Projections

(define-metafunction λcρ
  proj-struct : V X X natural -> (V ...)
  [(proj-struct (-- (struct X_m X_tag V ...)) X_m X_tag natural)
   ,(list-ref (term (V ...)) (term natural))]
  [(proj-struct (-- (struct X_m X_tag V ...) C_1 C_2 ...) X_m X_tag natural)
   ((remember-contract V_i C_i ...) ...)
   (where ((-- C_i ...) ...) (proj-left (-- C_1 C_2 ...)))
   (where V_i ,(list-ref (term (V ...)) (term natural)))]
  [(proj-struct (-- C_0 C ...) X_m X_tag natural)
   (proj-struct/a X_m X_tag natural ((join-contracts)) C_0 C ...)]
  [(proj-struct V) ()])


(define-metafunction λcρ
  proj-struct/a : X X natural ((-- C ...) ...) C ... -> (AV ...)
  [(proj-struct/a X_m X_tag natural (AV ...)) (AV ...)]
  [(proj-struct/a X_m X_tag natural (AV ...) ((rec/c X CON) ρ) C ...)
   (proj-struct/a X_m X_tag natural (AV ...) ((unroll (rec/c X CON)) ρ) C ...)]
  [(proj-struct/a X_m X_tag natural (AV ...) ((or/c CON_1 CON_2) ρ) C ...)
   (AV_1 ... AV_2 ...)
   (where (AV_1 ...) (proj-struct/a X_m X_tag natural (AV ...) (CON_1 ρ) C ...))
   (where (AV_2 ...) (proj-struct/a X_m X_tag natural (AV ...) (CON_2 ρ) C ...))]    
  [(proj-struct/a X_m X_tag natural (AV ...) ((struct/c X_m X_tag CON ...) ρ) C_2 ...)
   (proj-struct/a X_m X_tag natural ((remember-contract AV C) ...) C_2 ...)
   (where C (,(list-ref (term (CON ...)) (term natural)) ρ))]  
  [(proj-struct/a X_m X_tag natural (AV ...) C_0 C_1 ...)
   (proj-struct/a X_m X_tag natural (AV ...) C_1 ...)])

(test 
 (test-equal (term (proj-struct (-- ((struct/c p posn (pred string? f) (pred string? f)) (env))) p posn 0))
             (term ((-- ((pred string? f) (env)))))))

;; Project an V to the left
;; (proj-left (-- (cons/c exact-nonnegative-integer? string?) (cons/c zero? string?)))
;; ≡ (-- exact-nonnegative-integer? zero?)
(define-metafunction λcρ
  proj-left : V -> (V ...) 
  [(proj-left (-- (cons V_1 V_2))) (V_1)]
  [(proj-left (-- (cons V_1 V_2) C_1 C_2 ...))
   ((remember-contract V_1 C_left ...) ...)
   (where ((-- C_left ...) ...) (proj-left (-- C_1 C_2 ...)))]
  [(proj-left (-- C_0 C ...))
   (proj-left/a ((join-contracts)) C_0 C ...)]
  [(proj-left V) ()])

(define-metafunction λcρ
  proj-right : V -> (V ...)
  [(proj-right (-- (cons V_1 V_2))) (V_2)]
  [(proj-right (-- (cons V_1 V_2) C_1 C_2 ...))
   ((remember-contract V_2 C_right ...) ...)
   (where ((-- C_right ...) ...) (proj-right (-- C_1 C_2 ...)))]
  [(proj-right (-- C_0 C ...))
   (proj-right/a ((join-contracts)) C_0 C ...)]
  [(proj-right V) ()])

(define-metafunction λcρ
  proj-left/a : ((-- C ...) ...) C ... -> (AV ...)
  [(proj-left/a (AV ...)) (AV ...)]
  [(proj-left/a (AV ...) ((rec/c X CON) ρ) C ...)
   (proj-left/a (AV ...) ((unroll (rec/c X CON)) ρ) C ...)]
  [(proj-left/a (AV ...) ((or/c CON_1 CON_2) ρ) C ...)
   (AV_1 ... AV_2 ...)
   (where (AV_1 ...) (proj-left/a (AV ...) (CON_1 ρ) C ...))
   (where (AV_2 ...) (proj-left/a (AV ...) (CON_2 ρ) C ...))]
  [(proj-left/a (AV ...) ((cons/c CON_0 CON_1) ρ) C_2 ...)
   (proj-left/a ((remember-contract AV (CON_0 ρ)) ...) C_2 ...)]
  [(proj-left/a (AV ...) C_0 C_1 ...)
   (proj-left/a (AV ...) C_1 ...)])

(define-metafunction λcρ
  proj-right/a : ((-- C ...) ...) C ... -> (AV ...)
  [(proj-right/a (AV ...)) (AV ...)]
  [(proj-right/a (AV ...) ((rec/c X CON) ρ) C ...)
   (proj-right/a (AV ...) ((unroll (rec/c X CON)) ρ) C ...)]
  [(proj-right/a (AV ...) ((or/c CON_1 CON_2) ρ) C ...)
   (AV_1 ... AV_2 ...)
   (where (AV_1 ...) (proj-right/a (AV ...) (CON_1 ρ) C ...))
   (where (AV_2 ...) (proj-right/a (AV ...) (CON_2 ρ) C ...))]
  [(proj-right/a (AV ...) ((cons/c CON_0 CON_1) ρ) C_2 ...)
   (proj-right/a ((remember-contract AV (CON_1 ρ)) ...) C_2 ...)]
  [(proj-right/a (AV ...) C_0 C_1 ...)
   (proj-right/a (AV ...) C_1 ...)])

(test
 (test-equal (term (proj-left (-- (cons (-- (↓ 1 (env)) ((pred (prime? ^ f g) f) (env)))
                                        (-- (↓ 2 (env))))
                                  ((cons/c (pred (green? ^ f g) f)
                                           (pred (red? ^ f g) f))
                                   (env)))))
             (term ((-- (↓ 1 (env))
                        ((pred (prime? ^ f g) f) (env))
                        ((pred (green? ^ f g) f) (env)))))) 
 (test-equal (term (proj-left (-- ((∧) (env))
                                  ((cons/c (∧) (or/c (pred exact-nonnegative-integer? f)
                                                     (pred string? f))) (env)))))
             (term ((-- ((∧) (env))))))
 (test-equal (term (proj-right (-- (cons (-- (↓ 1 (env)) ((pred (prime? ^ f g) f) (env)))
                                         (-- (↓ 2 (env))))
                                   ((cons/c (pred (green? ^ f g) f)
                                            (pred (red? ^ f g) f))
                                    (env)))))
             (term ((-- (↓ 2 (env))
                        ((pred (red? ^ f g) f) (env))))))
 (test-equal (term (proj-right (-- ((∧) (env))
                                   ((cons/c (∧) (or/c (pred exact-nonnegative-integer? f)
                                                      (pred string? f))) (env)))))
             (term ((-- ((or/c (pred exact-nonnegative-integer? f)
                               (pred string? f))
                         (env)))))))

(define-metafunction λcρ
  list->list-value : (V ...) -> V
  [(list->list-value ())
   (-- (clos empty (env)))]
  [(list->list-value (V_1 V_2 ...))
   (-- (cons V_1 (list->list-value (V_2 ...))))])


(define-metafunction λcρ
  list-value->list : V -> (V ...)
  [(list-value->list (-- (clos empty ρ) C ...)) ()]
  [(list-value->list (-- (cons V_1 V_2) C ...))
   ,(cons (term V_1) (term (list-value->list V_2)))])

(define-metafunction λcρ
  amb : D D ... -> D
  [(amb D) D]
  [(amb D_1 D_3 ...)
   (if (-- ((pred (λ (x) #t) Λ) (env))) D_1 (amb D_3 ...))])

(define-metafunction λcρ
  amb/e : EXP EXP ... -> EXP
  [(amb/e EXP) EXP]
  [(amb/e EXP_1 EXP_3 ...)
   (if • EXP_1 (amb/e EXP_3 ...))])

(test
 ;; FIXME Why does this seemingly take FOREVER!?
 #;
 (redex-check λcρ (D_1 D_2) (term (amb D_1 D_2)))
 ;; Must be related to this; looks like a Redex bug:
 ;; EXHAUSTS ALL MEMORY
 #;
 (generate-term λcρ D_1 3))