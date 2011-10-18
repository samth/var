#lang racket
(require (except-in redex/reduction-semantics plug) (for-syntax syntax/parse))
(require (except-in "lang.rkt" final-state?) "flat-check.rkt" "meta.rkt" "alpha.rkt" "util.rkt" "annotate.rkt" "examples.rkt" 
         (only-in "step.rkt" lookup-modref/val lookup-modref/con))
(provide (except-out (all-defined-out) test))
(test-suite test cesk)

;; FIXME handling of cons, car, cdr is broken on pairs of functions.

(current-cache-all? #t)

(define exact? #t)

(define-extended-language CESK* λc~ 
  (K MT      
     (AP (clo ...) ((E ρ) ...) ℓ a)
     (IF E E ρ a)
     (OP o (clo ...) (E ...) ρ ℓ a)
     (LET x E ρ a)
     (BEG (E ρ) (E ρ) ... a)
     (CHK C ρ ℓ ℓ V-or-AE ℓ a)  ;; V?     
     (CHK-CONS C ρ ℓ ℓ V-or-AE ℓ V ρ a) ;; i hate the environment
     (CHK-OR V ρ (or/c FLAT HOC) ρ ℓ ℓ V-or-AE ℓ a)) ;; (if [] (rem V FLAT) (HOC <= V))     
   
  (ρ ((x a) ...))
  (clo (V ρ))
  (D clo K)
  (σ ((a {D ...}) ...))
  (ς (E ρ σ K)))

(define-metafunction CESK*
  widen : o V-or-B -> V-or-B
  [(widen o B) B]
  [(widen o V) 
   V
   (side-condition exact?)]
  [(widen o V) (widen/n 10 o V)])

(define-metafunction CESK*
  widen/n : nat o V -> V  
  [(widen/n nat o AV) AV]
  [(widen/n nat o (-- bool C ...)) (-- bool C ...)]
  [(widen/n nat first V) V]
  [(widen/n nat rest V) V]
  [(widen/n nat_0 o (-- nat C ...))
   (-- nat C ...)
   (side-condition (< (term nat) (term nat_0)))]
  [(widen/n nat_0 o (-- nat C ...)) (remember-contract (-- (nat/c)) C ...)]
  [(widen/n nat o (-- string C ...)) 
   (-- string C ...)
   (side-condition (< (string-length (term string)) (term nat_0)))]
  [(widen/n nat o (-- string C ...)) (remember-contract (-- (string/c)) C ...)]
  [(widen/n 0 o (-- (cons V_1 V_2) C ...))   
   (remember-contract (-- (pred cons? Λ)) C ...)]
  [(widen/n nat o (-- (cons V_1 V_2) C ...))
   (-- (cons (widen/n ,(sub1 (term nat)) o V_1) 
             (widen/n ,(sub1 (term nat)) o V_2))
       C ...)]
  [(widen/n nat o (-- empty C ...)) (-- empty C ...)]
  [(widen/n nat o (-- L C ...)) (-- L C ...)]
  [(widen/n nat o blessed-L) blessed-L]
  [(widen/n nat o blessed-A) blessed-A]  
  [(widen/n nat o (-- PV C ...)) (remember-contract (-- (any/c)) C ...)])

;; handles the second arg not being symbols
(define (variables-not-in* a bs)
  (variables-not-in a (map (λ (b) (if (symbol? b) b 'loc)) bs)))

(define-metafunction CESK*
  alloc-addr : σ (any ..._1) -> (any ..._1)
  [(alloc-addr σ (any ...))
   ,(variables-not-in* (term σ) (term (any ...)))
   (side-condition exact?)]
  [(alloc-addr σ (x ...)) 
   (x ...) #;
   ,(variables-not-in (term σ) (term (x ...)))]
  [(alloc-addr σ (K ...))
   ,(map (λ (p) (if (and (pair? p)) (car p) p)) (term (K ...)))]
  [(alloc-addr σ (V ...))
   ,(build-list (length (term (V ...))) values)])

(define-metafunction CESK*
  alloc : σ (any ..._1) -> (a ..._1)
  [(alloc σ (any ...))
   ((loc any_1) ...)
   (where (any_1 ...) (alloc-addr σ (any ...)))])

;; produces any/c if there's imprecision
(define-metafunction CESK*
  try-close-contract : C ρ σ -> C
  [(try-close-contract C ρ σ)
   C
   (where () (fv/C C))]
  [(try-close-contract C ρ σ) (any/c)])

;; produces (-- any/c) if there's imprecision
(define-metafunction CESK*
  try-close-value : V ρ σ -> V
  [(try-close-value V ρ σ)
   V
   (where () (fv V))]
  [(try-close-value V ρ σ) (-- (any/c))])


(define-metafunction CESK*
  extend-env : ρ (x ..._1) (a ..._1) -> ρ
  [(extend-env ((x_0 a_0) ...) (x ..._1) (a ..._1))
   ((x a) ... (x_0 a_0) ...)])

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

#;
(define-metafunction CESK*
  load : E -> ς
  [(load E)
   (E () () MT)])

(define-metafunction CESK*
  load : any -> any
  [(load any)
   ,(st (term any) '() '() 'MT)])

;; this will stop working once there's real non-determinism
(define-metafunction CESK*
  plug : E K -> E
  [(plug E MT) E]
  [(plug E (IF E_1 E_2 ρ a)) (if E E_1 E_2)]
  [(plug E (OP o (V ρ_1) ... E_1 ... ρ ℓ a))
   (@ o V ... E E_1 ... ℓ)]
  [(plug E (AP ((V ρ_1) ...) ((E_1 ρ) ...) ℓ a))
   (@ V ... E E_1 ... ℓ)]
  [(plug E (LET x E_1 ρ a))
   (let x E E_1)]
  [(plug E (BEG (E_1 ρ) a)) ;; this is dead anyway
   (begin E E_1)]
  [(plug E (CHK C ρ ℓ_1 ℓ_2 V ℓ_3 a))
   (C <= ℓ_1 ℓ_2 V ℓ_3 E)])

(define-metafunction CESK*
  addr-of : K -> a
  ;; the address always goes last!
  [(addr-of (any ... a)) a])

(define-metafunction CESK*
  unload : ς -> E
  [(unload (E ρ σ MT))
   E]
  [(unload (E ρ σ K))
   (unload ((plug E K) ρ σ K_1))
   (where {D_0 ... K_1 D_1 ...} (sto-lookup σ (addr-of K)))])

(struct st (c e s k) #:prefab)
(struct S (name results) #:prefab)

(define V? (redex-match CESK* V))

(define-match-expander V:
  (syntax-parser
   [(_ pat) #'(? V? pat)]))

(define (combine-S . ss)
  (match ss
    [(list) (S #f null)]
    [(list (S name results))
     (S name results)]
    [(list (S name results) ...)
     (S 'multi-rule
        (apply append results))]))

(define-syntax-rule (choose [tst . rhs] ...)
  (apply combine-S
         (filter values (list (and tst (let () . rhs)) ...))))

(define (step* state)
  (match state    
    
    [(st (V: V) ρ σ `(AP ,clo ((,E_0 ,ρ_0) ,rest ...) ,ℓ ,a))
     (S 'ap-next
        (list (st E_0 ρ_0 σ `(AP (,@clo (,V ,ρ)) ,rest ,ℓ ,a))))]
    [(st (V: V) ρ σ `(OP ,o ,clo (,E_0 ,rest ...) ,ρ_0 ,ℓ ,a))
     (S 'op-next
        (list (st E_0 ρ_0 σ `(OP ,o (,@clo (,V ,ρ)) ,rest ,ρ_0 ,ℓ ,a))))]
    
    [(st `(@ ,(? (redex-match CESK* op) op) ,E_0 ,E_1 ... ,ℓ) ρ σ K)
     (S 'op-push
        (for/list ([a (term (alloc ,σ (,K)))])
          (define σ_0 (term (extend-sto1 ,σ ,a ,K)))
          (st E_0 ρ σ_0 `(OP ,op () ,E_1 ,ρ ,ℓ ,a))))]
    
    [(st `(@ ,E_0 ,E_1 ... ,ℓ) ρ σ K)
     (S 'ap-push
        (for/list ([a (term (alloc ,σ (,K)))])
          (define σ_0 (term (extend-sto1 ,σ ,a ,K)))
          (st E_0 ρ σ_0 `(AP () ,(map (λ (e) (list e ρ)) E_1) ,ℓ ,a))))]
    
    [(st `(if ,E_0 ,E_1 ,E_2) ρ σ K)
     (S 'if-push
        (for/list ([a (term (alloc ,σ (,K)))])
          (define σ_0 (term (extend-sto1 ,σ ,a ,K)))
          (st E_0 ρ σ_0 `(IF ,E_1 ,E_2 ,ρ ,a))))]
    
    
    ;; begin
   [(st (V: V) ρ σ `(BEG (,E ,ρ_0) ,a))
    (S 'begin-done
       (for/list ([K (term (sto-lookup ,σ ,a))])
         (st E ρ_0 σ K)))]
   
   [(st (V: V) ρ σ `(BEG (,E ,ρ_0) ,rest ... ,a))
    (S 'begin-swap 
       (list (st E ρ_0 σ `(BEG ,@rest ,a))))]
   
   ;; let
    [(st (V: V) ρ σ `(LET . ,_)) (error "let is broken in the machine")]
    
    [(st (? symbol? x) ρ σ K)
     (S 'var
        (for/list ([D (in-list (term (sto-lookup ,σ (env-lookup ,ρ ,x))))])
          (match D
            [(list V ρ_0) (st V ρ_0 σ K)])))]
    [(st (? (redex-match CESK* PV) pv) ρ σ K)
     (S 'wrap (list (st `(-- ,pv) ρ σ K)))]
    
    ;; nullary application
    [(st (V: V-proc) ρ σ `(AP () () ,ℓ ,a))
     (match V-proc
       [`(-- (λ ,rec () ,E) ,C ...)
        (S 'β-0 
           (for/list ([K (term (sto-lookup ,σ ,a))])
             (st E ρ σ K)))]
       [(and fun `(-- (λ ,rec () ,E) ,C ...))
        (S 'β-rec-0 
           (for*/list ([K (term (sto-lookup ,σ ,a))]
                       [a_1 (term (alloc ,σ (,rec)))])          
             (st E
                 (term (extend-env ,ρ (,rec) (,a_1)))
                 (term (extend-sto1 ,σ ,a_1 ,(list fun ρ)))
                 K)))]
       ;; these next two cases are identical
       [`((--> (λ () ,C)) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_f))
        (S 'nullary-blessed-β-dep
           (for/list ([clo (term (sto-lookup ,σ ,a_f))])
             (match-let* ([K `(CHK ,C ,ρ ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]
                          [`(,V_f ,ρ_f) clo]
                          [`(,a_k) (term (alloc ,σ (,K)))]
                          [σ_1 (term (extend-sto1 ,σ ,a_k ,K))])
               (st V_f ρ_f σ_1 `(AP () () ,ℓ ,a_k)))))]
       [`((--> ,C) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_f))
        (S 'nullary-blessed-β
           (for/list ([clo (term (sto-lookup ,σ ,a_f))])
             (match-let* ([K `(CHK ,C ,ρ ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]
                          [`(,V_f ,ρ_f) clo]
                          [`(,a_k) (term (alloc ,σ (,K)))]
                          [σ_1 (term (extend-sto1 ,σ ,a_k ,K))])
               (st V_f ρ_f σ_1 `(AP () () ,ℓ ,a_k)))))]
       [_ 
        (choose [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
                      (equal? 0 (term (arity ,V-proc))))
                 "abstract beta-0"]
                [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
                      (not (equal? 0 (term (arity ,V-proc)))))
                 (S 'blame-arity
                    (for/list ([K (term (sto-lookup ,σ ,a))])
                      (st `(blame ,ℓ  Λ ,V-proc λ ,V-proc) ρ σ K)))]
                [(and (term (∈ #f (δ (@ procedure? ,V-proc ★)))))
                 (S 'blame-not-proc
                    (for/list ([K (term (sto-lookup ,σ ,a))])
                      (st `(blame ,ℓ  Λ ,V-proc λ ,V-proc) ρ σ K)))])])]
    
    ;; unary+ application
    [(st (V: V) ρ σ `(AP ((,(V: V-proc) ,ρ_0) ,clo ...) () ,ℓ ,a))
     (choose 
       [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
             (equal? (add1 (length (term ,clo)))
                     (term (arity ,V-proc))))
        (match V-proc
          [`(-- (λ ,rec (,x ...) ,E) ,C ...)
           (define a1s (term (alloc ,σ ,(cons rec x))))        
           (S 'β-rec
              (for/list ([K (term (sto-lookup ,σ ,a))])
                (st E 
                    (term (extend-env ,ρ_0 ,(cons rec x) ,a1s))
                    (term (extend-sto ,σ ,a1s ,(cons `((-- (λ ,rec ,x ,E) ,@C) ,ρ_0)
                                                     (append clo (list (list V ρ))))))
                    K)))]
          [`(-- (λ (,x ...) ,E) ,C ...)
           (define a1s (term (alloc ,σ ,x)))
           (S 'β
              (for/list ([K (term (sto-lookup ,σ ,a))])
                (st E 
                    (term (extend-env ,ρ_0 ,x ,a1s))
                    (term (extend-sto ,σ ,a1s ,(append clo (list (list V ρ)))))
                    K)))]
          [`((,C_0 ... --> ,C_1) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_f))
           (printf "got here \n")
           (match-let* ([K `(CHK ,C_1 ,ρ ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]
                        [(list a_k) (term (alloc ,σ (,K)))]
                        [σ_1 (term (extend-sto1 ,σ ,a_k ,K))]
                        [K2 `(AP ()
                                 ,(for/list ([clo_1 (cons (list V ρ) clo)]
                                             [C_0* C_0])
                                    (match-let ([(list V_2 ρ_2) clo_1])
                                      `((,C_0* <= ,ℓ_2 ,ℓ_1 ,V_2 ,ℓ_3 ,V_2) ,ρ_2)))
                                 ,ℓ ,a_k)])
             (S 'unary+-blessed-β
                (for/list ([clo_1 (term (sto-lookup ,σ ,a_f))])
                  (match-define (list V_f ρ_f) clo_1)
                  (st V_f ρ_f σ_1 K2))))]
          [_ "abstract beta"])]
       [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
             (not (equal? (add1 (length (term ,clo)))
                          (term (arity ,V-proc)))))
        (S 'blame-arity
           (for/list ([K (term (sto-lookup ,σ ,a))])
             (st `(blame ,ℓ  Λ ,V-proc λ ,V-proc) ρ_0 σ K)))]
       [(term (∈ #f (δ (@ procedure? ,V-proc ★)))) 
        (S 'blame-not-proc
           (for/list ([K (term (sto-lookup ,σ ,a))])
             (st `(blame ,ℓ  Λ ,V-proc λ ,V-proc) ρ_0 σ K)))])]

    
    
    [(st (V: V) ρ σ `(IF ,E_1 ,E_2 ,ρ_1 ,a))     
     (S 'if
        (for*/list ([K (term (sto-lookup ,σ ,a))]
                    [r (term (δ (@ false? ,V ★)))]
                    [r* (in-value (match r [`(-- ,(? boolean? a)) a] [else 0]))]
                    #:when (boolean? r*))
          (st (if (not r*) E_1 E_2) ρ_1 σ K)))]
    ;; δ
   ;; FIXME broken delta rule for things producing closures.
    [(st (V: V) ρ σ `(OP ,op ,(list (list V_0 ρ_0) ...) () ,ρ_1 ,ℓ ,a))
     (S 'δ
        (for*/list ([K (term (sto-lookup ,σ ,a))]
                    [V-or-B (term (δ ,`(@ ,op ,@V_0 ,V ,ℓ)))])
          (st (term (widen ,op ,V-or-B)) '() σ K)))]
    
    [(st `(begin ,E_0 ,E_1) ρ σ K)
     (S 'beg-push
        (match-let ([(list a) (term (alloc ,σ (,K)))])
          (define σ_0 (term `(extend-sto1 ,σ ,a ,K)))
          (st E_0 ρ σ_0 `(BEG (,E_1 ρ) ,a))))]
    
    [(st `(let ,x ,E_0 ,E_1) ρ σ K)
     (S 'let-push
        (match-let ([(list a) (term (alloc ,σ (,K)))])
          (define σ_0 (term `(extend-sto1 ,σ ,a ,K)))
          (st E_0 ρ σ_0 `(LET ,x ,E_1 ,ρ ,a))))]
    
    [(st `(,C <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,E) ρ σ K)
     (match-let* ([`(,a) (term (alloc ,σ (,K)))]
                  [σ_0 (term (extend-sto1 ,σ ,a ,K))])
         (S 'chk-push 
            (list (st E ρ σ_0
                      `(CHK ,C ,ρ ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)))))]
    
    [(st (V: V) ρ σ `(CHK (,C ... -> ,result) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (choose
      [(term (∈ #t (δ (@ procedure? ,V ★))))
       (S 'chk-fun-pass
        (match-let* ([(list a_new) (term (alloc ,σ (,V)))]
                     [σ_1 (term (extend-sto1 ,σ ,a_new (,V ,ρ)))])
          (for/list ([K (term (sto-lookup ,σ ,a))])
            (st `((,@C --> ,result) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_new)) ρ_1 σ_1 K))))]
      [(term (∈ #f (δ (@ procedure? ,V ★))))
       (S 'chk-fun-fail-fail
          (for/list ([K (term (sto-lookup ,σ ,a))])
            (st `(blame ,ℓ_1 ,ℓ_3 ,V-or-AE (,@C -> ,result) ,V) ρ σ K)))])]
    
    [(st (V: V) ρ σ `(CHK (rec/c ,X ,HOC) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (S 'chk-unroll
        (list (st V ρ σ `(CHK ,(term (unroll (rec/c ,X ,HOC))) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))))]
    
    [(st (V: V) ρ σ `(CHK ,(? (redex-match CESK* FLAT) FLAT) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (match-let* ([K
                   `(IF ,(term (remember-contract ,V (try-close-contract ,FLAT ,ρ_1 ,σ)))
                       (blame ,ℓ_1 ,ℓ_3 ,V-or-AE ,FLAT ,V)
                       ,ρ ,a)]
                  [(list a_k) (term (alloc ,σ (,K)))]
                  [σ_new (term (extend-sto1 ,σ ,a_k ,K))])
       (S 'flat-check
          (list (st V ρ σ_new
                    `(AP (((-- ,(term (flat-check ,FLAT ,V))) ,ρ_1)) () Λ ,a_k)))))]
    
    [a (printf "catchall: ~a\n" a) (S #f null)]))

(define (factorial n)
  (if (zero? n) 1 (* n (factorial (sub1 n)))))

(define step
  (reduction-relation
   CESK*
   (--> any_in any_out
        (where any_S ,(step* (term any_in)))
        (where (any_1 ... any_out any_2 ...) ,(S-results (term any_S)))
        (computed-name (S-name (term any_S))))))
#;
(define step
  (reduction-relation
   CESK* #:domain ς
   
   ;; Reductions
      
  
   ;; Blessing
   
           
   
   ;; BLESSED APPLICATION
   ;; Nullary blessed application
   
   
   ;; Unary+ blessed application
   ;; FIXME: these two rules are broken with the environments of the argument contracts.
   ;; need a new kind of continuation to solve. (Lucky for just unary case in paper, it works).
   
   (--> (V_n ρ_n σ (AP ((((C_0 ... --> (λ (x ...) C_1)) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 (addr a_f)) ρ)
                        (V_1 ρ_1) ...)
                       ()
                       ℓ a))
        (V_f ρ_f σ_1 
             (AP ()
                 (((C_0 <= ℓ_2 ℓ_1 V_2 ℓ_3 V_2) ρ_2) ...)
                 ℓ a_k))
        (side-condition (= (length (term (C_0 ...)))
                           (add1 (length (term ((V_1 ρ_1) ...))))))
        (where (D_0 ... (V_f ρ_f) D_1 ...) (sto-lookup σ a_f))
        (where (a_1 ...) (alloc σ (x ...)))
        (where ((V_2 ρ_2) ...) ,(reverse (term ((V_1 ρ_1) ... (V_n ρ_n)))))
        (where ρ_3 (extend-env ρ (x ...) (a_1 ...)))
        (where K (CHK C_1 ρ_3 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        (where (a_k) (alloc σ (K)))        
        (where σ_1 (extend-sto σ (a_k a_1 ...) (K (V_2 ρ_2) ...)))
        unary+-blessed-β-dep)
             
   ;; CONTRACT CHECKING   
   
   
   
   
   (--> (V ρ σ (CHK (or/c FLAT HOC) ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        (V ρ σ_new
           (AP (((-- (flat-check FLAT V)) ρ_1)) () Λ a_k))        
        (where K (CHK-OR V ρ (or/c FLAT HOC) ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        (where (a_k) (alloc σ (K)))
        (where σ_new (extend-sto1 σ a_k K))
        check-or-pass)
   
   (--> (V ρ_0 σ (CHK-OR U ρ (or/c FLAT HOC) ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))        
        (U ρ σ (CHK HOC ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        (where #t (∈ #t (δ (@ false? V Λ))))
        check-or-false)
   
   (--> (V ρ_0 σ (CHK-OR U ρ (or/c FLAT HOC) ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        ((remember-contract U (try-close-contract FLAT ρ_1)) ρ σ K)        
        (where #t (∈ #f (δ (@ false? V Λ))))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        check-or-true)
   
   (--> (V ρ σ (CHK (and/c C_0 C_1) ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        (V ρ σ_1 (CHK C_0 ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a_1))                
        (where HOC (and/c C_0 C_1))
        (where K (CHK C_1 ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        (where (a_1) (alloc σ (K)))        
        (where σ_1 (extend-sto1 σ a_1 K))
        check-and-push)
   
   (--> ((-- (cons V_0 V_1) C ...) ρ σ (CHK (cons/c C_0 C_1) ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
        (V_0 ρ σ_new (CHK C_0 ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a_k))
        (where K (CHK-CONS C_1 ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 V_1 ρ a))
        (where (a_k) (alloc σ (K)))
        (where σ_new (extend-sto1 σ a_k K))
        (where HOC (cons/c C_0 C_1))
        check-cons-pass-first)
   
   (--> (V ρ σ (CHK-CONS C_1 ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 V_1 ρ_2 a))
        (V_1 ρ_2 σ_new (CHK C_1 ρ_1 ℓ_1 ℓ_2 V-or-AE ℓ_3 a_k))
        (where K (OP cons (V ρ) () Λ a))
        (where (a_k) (alloc σ (K)))
        (where σ_new (extend-sto1 σ a_k K))
        check-cons-pass-rest)   
   
   ;; Nullary abstract application
   (--> (AV ρ_0 σ (AP () () ℓ a))
        ((remember-contract (-- (any/c)) (try-close-contract C_0 ρ_0 σ) ...) () σ K)
        (side-condition (term (∈ #t (δ (@ procedure? AV ★)))))
        (side-condition (equal? 0 (term (arity AV))))        
        (where (-- C ...) AV)
        (where (C_0 ...) (range-contracts (C ...) ()))
        (where {D_0 ... K D_1 ...} (sto-lookup σ a))
        apply-abs0)
   
   ;; applying abstract values   
   (--> (V ρ σ (AP ((AV ρ_1) clo ...) () ℓ a))
        ((amb (-- 0) (demonic* C_demon U)) ρ_2 σ (BEG (E_result ()) a))
        (where (clo_0 ..._1 (U ρ_2) clo_1 ..._2) ((V ρ) clo ...))
        (side-condition (term (∈ #t (δ (@ procedure? AV ★)))))
        (side-condition (equal? (length (term (clo ... V)))
                                (term (arity AV))))
        (where (-- C ...) AV)
        (where ((C_D ...) ...) (domain-contracts (C ...)))
        (where (C_demon0 ..._1 C_demon C_demon1 ..._2) ((∧ C_D ...) ...))
        (where ((V_0 ρ_0) ...) (clo ... (V ρ)))
        (where (V_0c ...) ((try-close-value V_0 ρ_0 σ) ...))
        (where (C_0 ...) (range-contracts (C ...) (V_0c ...)))
        (where E_result (remember-contract (-- (any/c)) (try-close-contract C_0 ρ_1 σ) ...))
        ;; FIXME, closing contracts in their environments
        ;; because we don't have contract closures.
        
        apply-abs-known-arity)
   
   (--> (V ρ σ (AP ((AV ρ_1) clo ...) () ℓ a))
        ((amb (-- 0) (demonic* (any/c) U)) ρ_2 σ (BEG ((-- (any/c)) ()) a))
        (where (clo_0 ... (U ρ_2) clo_1 ...) ((V ρ) clo ...))
        (side-condition (term (∈ #t (δ (@ procedure? AV ★)))))
        (side-condition ;; this is a proc with no arity, so it could be anything
         (not (term (arity AV))))
        apply-abs-no-arity)
   
   ;; SPLITTING OR/C and REC/C ABSTRACT VALUES
   ;; Some introduced values are infeasible, which is still sound.
   (--> ((-- C_0 ... (or/c C_1 ... C_2 C_3 ...) C ...) ρ σ K)
        ((remember-contract (-- (any/c) C_0 ... C ...) C_2) ρ σ K)
        (side-condition (term (valid? C_2)))
        abs-or/c-split)
   
   (--> ((-- C_0 ... (rec/c x C_1) C ...) ρ σ K)  ;; Productivity implies this doesn't loop.
        ((remember-contract (-- (any/c) C_0 ... C ...) (unroll (rec/c x C_1))) ρ σ K)
        (side-condition (term (valid? (rec/c x C_1))))
        abs-rec/c-unroll)   
   
   ;; Context shuffling   
   
   (--> ((C <= ℓ_1 ℓ_2 x ℓ_3 E) ρ σ K)
        ((C <= ℓ_1 ℓ_2 V ℓ_3 E) ρ σ K)
        (where (D_0 ... (V ρ_0) D_1 ...)
               (sto-lookup σ (env-lookup ρ x)))
        chk-subst)
   
   ))

(define (st->list s)
  (match s
    [(st a b c d) (list a b c d)]))


(define (∆ Ms)
  (reduction-relation
   CESK* 
   (--> any_in
        ,(st (term (-- PV)) (st-e (term any_in)) (st-s (term any_in)) (st-k (term any_in)))
        (where (f_1 ^ f f) ,(st-c (term any_in)))
        (where PV (lookup-modref/val f f_1 ,Ms))
        Δ-self)
   (--> any_in
        ,(st (term (C <= f ℓ (-- PV) f_1 (-- PV))) (st-e (term any_in)) (st-s (term any_in)) (st-k (term any_in)))
        (where (f_1 ^ ℓ f) ,(st-c (term any_in)))
        (where C (lookup-modref/con f f_1 ,Ms))
        (where PV (lookup-modref/val f f_1 ,Ms))
        (side-condition (not (eq? (term f) (term ℓ))))
        Δ-other)))

(define (Δ~ Ms)
  (union-reduction-relations
   (∆ Ms)
   (reduction-relation
    CESK*
    (--> any_in
         ,(st (term (C <= f ℓ (-- C) f_1 (remember-contract (-- (any/c)) C)))
              (st-e (term any_in)) (st-s (term any_in)) (st-k (term any_in)))
         (where (f_1 ^ ℓ f) ,(st-c (term any_in)))
         (where bullet (lookup-modref/val f f_1 ,Ms))
         (where C (lookup-modref/con f f_1 ,Ms))
         (side-condition (not (eq? (term f) (term ℓ))))
         ∆-opaque))))

(define error-propagate
  (reduction-relation 
   CESK*
   (--> any_in 
        ,(st (term B) '() (term (gc (B () σ MT))) 'MT)
        (where B ,(st-e (term any_in)))
        (side-condition (not (equal? (st-k (term any_in)) (term MT))))
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

(test
 (redex-check CESK* (E ρ)
              (redex-match CESK* (a ...) (term (live-loc-clo (E ρ))))))

(define-metafunction CESK*
  live-loc-env : ρ -> (a ...)
  [(live-loc-env ((x a) ...))
   (a ...)])

(test
 (redex-check CESK* ρ
              (redex-match CESK* (a ...) (term (live-loc-env ρ)))))

(define-metafunction CESK*
  live-loc-E : any_E -> (a ...)
  [(live-loc-E (loc any)) ((loc any))]
  ;; don't traverse the orig value in any of these
  [(live-loc-E (any_C <= ℓ_1 ℓ_2 any_V ℓ_2 any_E)) (live-loc-E (any_C any_E))]
  [(live-loc-E (CHK any_C any_ρ ℓ_1 ℓ_2 any_V ℓ_2 any_E any_ρ2 any_a)) (live-loc-E (any_C any_ρ any_E any_ρ2 any_a))]
  [(live-loc-E (blame ℓ_1 ℓ_2 any_V any_C any_V2)) (live-loc-E (any_C any_V2))]
  [(live-loc-E (addr a)) (a)]
  [(live-loc-E (any ...))
   (a ... ...)
   (where ((a ...) ...) ((live-loc-E any) ...))]
  [(live-loc-E any) ()])

(test
 (redex-check CESK* E
              (redex-match CESK* (a ...) (term (live-loc-E E)))))  

(define (subset-of a b) (subset? (apply set a) (apply set b)))

(define-metafunction CESK*
  live-loc-K : K -> (a ...) 
  [(live-loc-K MT) ()]
  [(live-loc-K (AP (clo ...) ((E ρ) ...) ℓ a))
   (a a_0 ... ... a_1 ... ...)
   (where ((a_0 ...) ...) ((live-loc-clo clo) ...))
   (where ((a_1 ...) ...) ((live-loc-clo (E ρ)) ...))]
  [(live-loc-K (IF E_1 E_2 ρ a)) 
   (a a_0 ... a_1 ...)
   (where (a_0 ...) (live-loc-clo (E_1 ρ)))
   (where (a_1 ...) (live-loc-clo (E_2 ρ)))]    
  [(live-loc-K (OP o (clo ...) (E ...) ρ ℓ a)) 
   (a a_0 ... ... a_1 ... ...)
   (where ((a_0 ...) ...) ((live-loc-clo clo) ...))
   (where ((a_1 ...) ...) ((live-loc-clo (E ρ)) ...))]
  [(live-loc-K (LET x E ρ a))
   (a a_0 ...)
   (where (a_0 ...) (live-loc-clo (E ρ)))]
  [(live-loc-K (BEG (E ρ) ... a))
   (a a_0 ... ...)
   (where ((a_0 ...) ...) ((live-loc-clo (E ρ)) ...))]
  ;; Probably want V-or-AE to be a closure and traverse it as well.
  [(live-loc-K (CHK C ρ ℓ_0 ℓ_1 V-or-AE ℓ_2 a))
   (a a_0 ... a_1 ...)
   (where (a_0 ...) (live-loc-E C))
   (where (a_1 ...) (live-loc-env (restrict ρ (fv/C C))))]
  [(live-loc-K (CHK-OR V ρ C ρ_2 ℓ_1 ℓ_2 V-or-AE ℓ_3 a))
   (a a_0 ... a_1 ... a_2 ...)
   (where (a_0 ...) (live-loc-E C))
   (where (a_2 ...) (live-loc-clo (V ρ)))
   (where (a_1 ...) (live-loc-env (restrict ρ_2 (fv/C C))))]
  [(live-loc-K (CHK-CONS C ρ ℓ_0 ℓ_1 V-or-AE ℓ_2 V ρ_2 a))
   (a a_0 ... a_1 ... a_2 ...)
   (where (a_0 ...) (live-loc-E C))
   (where (a_2 ...) (live-loc-clo (V ρ_2)))
   (where (a_1 ...) (live-loc-env (restrict ρ (fv/C C))))])

(test
 (redex-check CESK* K
              (redex-match CESK* (a ...) (term (live-loc-K K)))))

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

(test
 (redex-check CESK* (D ...)
              (redex-match CESK* (a ...) (term (live-loc-Ds (D ...))))))

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
  (reduction-relation 
   CESK*
   [--> any_old ,(st (term E) (term ρ_1) (term σ_1) (term K))
        (where (any_name (any_1 ... any_state any_2 ...))
               ,(match (step* (term any_old)) [(S n r) (displayln (list n r)) (list n r)]))
        (where (E ρ σ K) ,(match (term any_state) [(struct st (E1 ρ1 σ1 K1))
                                                   (displayln (list E1 ρ1 σ1 K1))
                                                   (list E1 ρ1 σ1 K1)]))
        (where σ_1 (gc (E ρ σ K)))
        (where ρ_1 (restrict ρ (fv E)))
        (computed-name (term any_name))]))

(define (stepΔ-gc Ms) 
  (union-reduction-relations error-propagate step-gc (Δ~ Ms)))

(define (final-state? s)
  (and (eq? 'MT (st-k s))
       (or (redex-match CESK* V (st-c s))
           (redex-match CESK* B (st-c s)))))


(define ((colorize Ms) x node)
  (define opaques (filter-map (λ (M) (match M
                                       [(list 'module n lang (list 'define _ ☁) ... prov) n]
                                       [_ #f]))
                              Ms))
  (cond [(redex-match CESK* (V any any_1 MT) x) "green"]
        [(and (st? x) 
              (eq? 'MT (st-k x))
              (redex-match CESK* V (st-c x))) "green"]
        [(redex-match CESK* (B any any_1 MT) x)
         (redex-let CESK*
                    ([(blame ℓ ℓ_0 V C-ext V_0) (car x)])
                    (cond [(equal? (term ℓ) '★) "pink"]
                          [(member (term ℓ) opaques) "pink"]
                          [else "red"]))]
        [(null? (term-node-children node)) "blue"]
        [else #t]))

(define-syntax-rule (trace-it P . rest)
  (traces (stepΔ-gc (program-modules P))
          (term (load ,(last P)))
          #:pred (colorize (program-modules P))
          . rest))



(define (step-fixpoint P)
  (let ([l (term (load* ,(last P)))])
    (let loop ([terms (list l)] [finals (set)])
      (cond [(null? terms) (remove-duplicates (for/list ([f finals]) (st-c f)))]
            [else
             (define new-terms
               (append-map (λ (t) (S-results (step* t))) terms))
             (define-values (f t) (partition final-state? new-terms))
             (loop (remove-duplicates t) (set-union finals (apply set f)))]))))

#|
(trace-it fit-example)
(trace-it fit-example-rsa-7)
(trace-it fit-example-keygen-string)
(trace-it example-8)
(trace-it example-8-opaque)
(trace-it list-id-example)
(trace-it (term (annotator ,cons/c-example-raw)))
|#

(define-syntax (print-here stx)
  (syntax-case stx ()
    [(_ foo)
     #`(displayln #,(syntax-line #'foo))]))

(define-syntax-rule (test-->>p P e ...)
  (begin (print-here P)
  (test-->>E (stepΔ-gc (program-modules P))
            ;#:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2))))
            ;#:cycles-ok
            (term (load ,(last P)))
            (term (load ,e))) ...))

(define-syntax-rule (test-->>pE P e ...)
  (test-->>E (stepΔ-gc (program-modules P))
             #;#;
             #:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2))))
             (term (load ,(last P)))
             (term (load ,e)) ...))

(define-syntax-rule (test-->>c r t1 t2)
  (test-->> r #:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2)))) (term (load ,t1)) (term (load ,t2))))

(test
 (test-->>c step-gc (term (@ (-- (λ (x) 0)) (-- 1) †)) (term (-- 0)))
 #; ;; this loops
 (test-->>c v 
            (term (@ (-- (λ f (x) (@ f x †))) (-- 0) †))
            (term (@ (-- (λ f (x) (@ f x †))) (-- 0) †))) 
 
 (test-->>c step-gc (term (@ (-- 0) (-- 1) †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test-->>c step-gc (term (if (-- 0) 1 2)) (term (-- 1)))
 (test-->>c step-gc (term (if (-- #t) 1 2)) (term (-- 1)))
 (test-->>c step-gc (term (if (-- #f) 1 2)) (term (-- 2)))
 (test-->>c step-gc (term (@ add1 (-- 0) †)) (term (-- 1)))
 (test-->>c step-gc (term (@ procedure? (-- #f) †)) (term (-- #f)))
 (test-->>c step-gc (term (@ procedure? (-- (λ (x) x)) †)) (term (-- #t)))
 (test-->>c step-gc (term (@ procedure? (-- (λ f (x) x)) †)) (term (-- #t)))
 (test-->>c step-gc (term (@ procedure? (-- ((any/c) -> (any/c))) †)) (term (-- #t)))
 (test-->>c step-gc (term (@ cons (-- 1) (-- 2) †)) (term (-- (cons (-- 1) (-- 2)))))
 
 (test-->>c step-gc (term (@ (λ (x) 0) 1 †)) (term (-- 0)))                
 (test-->>c step-gc (term (@ 0 1 †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test-->>c step-gc (term (if 0 1 2)) (term (-- 1)))
 (test-->>c step-gc (term (if #t 1 2)) (term (-- 1)))
 (test-->>c step-gc (term (if #f 1 2)) (term (-- 2)))
 (test-->>c step-gc (term (@ add1 0 †))  (term (-- 1)))
 (test-->>c step-gc (term (@ procedure? #f †)) (term (-- #f)))
 (test-->>c step-gc (term (@ cons 1 2 †)) (term (-- (cons (-- 1) (-- 2))))))


(test
 (test-->>c step-gc (term (@ (λ () 4) f)) (term (-- 4)))
 (test-->>c step-gc (term (@ (λ z () 4) f)) (term (-- 4)))
 (test-->>c step-gc (term (@ (-- (-> (nat/c))) f)) (term (-- (nat/c))))
 (test-->>c step-gc (term ((nat/c) <= f g (-- 0) f (-- 5))) (term (-- 5)))
 (test-->>c step-gc 
            (term ((nat/c) <= f g (-- 0) f (-- (λ (x) x))))
            (term (blame f f (-- 0) (nat/c) (-- (λ (x) x)))))
 (test-->>c step-gc 
            (term ((nat/c) <= f g (-- 0) f (-- #t))) 
            (term (blame f f (-- 0) (nat/c) (-- #t))))
 (test-->>c step-gc 
            (term (((any/c)  -> (any/c)) <= f g (-- 0) f (-- (λ (x) x))))
            ;; kind of a giant hack
            (term (((any/c) --> (any/c)) <= f g (-- 0) f (addr ,(car (term (alloc ([(loc 0) (((-- 0) ()))]) ((-- (λ (x) x))))))))))
 (test-->>c step-gc 
            (term (((any/c)  -> (any/c)) <= f g (-- 0) f (-- 5)))
            (term (blame f f (-- 0) ((any/c) -> (any/c)) (-- 5))))
 (test-->>c step
            (term ((pred (λ (x) 0) ℓ) <= f g (-- 0) f (-- 5)))
            (term (-- 5 (pred (λ (x) 0) ℓ))))
 (test-->>c step
            (term ((and/c (nat/c) (empty/c)) <= f g (-- 0) f (-- #t)))
            (term (blame f f (-- 0) (and/c (nat/c) (empty/c)) (-- #t)))))






(test 
 ;; testing demonic
 (test-->>pE (term (annotator [(simple-module p ((cons/c exact-nonnegative-integer? exact-nonnegative-integer?) . -> . exact-nonnegative-integer?) ☁)                         
                         (require (only-in p p))
                         (p (cons 1 2))]))
             (term (-- (pred exact-nonnegative-integer? p)))) 
 (test-->>p (term (annotator [(simple-module p ((and/c exact-nonnegative-integer? exact-nonnegative-integer?) . -> . exact-nonnegative-integer?) ☁)
                        (require (only-in p p))
                        (p 1)]))
            (term (-- (pred exact-nonnegative-integer? p))))
 (test-->>p (term (annotator [(simple-module p ((or/c exact-nonnegative-integer? exact-nonnegative-integer?) . -> . exact-nonnegative-integer?) ☁)
                        (require (only-in p p))
                        (p 1)]))
            (term (-- (pred exact-nonnegative-integer? p)))) 
 (test-->>p (term [(require) ((string/c) <= |†| rsa (-- "Plain") rsa (-- "Plain"))])
            (term (-- "Plain"))) 
 #; ;; unbound module var
 (test-->>p (term [(@ (-- (λ (o) (b ^ o))) (-- "") sN)])
            (term (b ^ o))) 
 (test-->>p (term [(require) (@ (-- (λ (o) (@ 4 5 o))) (-- "") sN)])
            (term (blame o Λ (-- 4) λ (-- 4))))
 (test-->>p (term (annotator [(simple-module n (and/c exact-nonnegative-integer? exact-nonnegative-integer?) 1) (require (only-in n n)) n]))
            (term (-- 1))) 
 (test-->>p (term (annotator [(simple-module n (and/c exact-nonnegative-integer? (pred (λ (x) (= x 7)))) 7) (require (only-in n n)) n]))
            (term (-- 7 (pred (λ (x) (@ = x 7 n)) n)))) 
 (test-->>p (term (annotator [(simple-module n (and/c exact-nonnegative-integer? (pred (λ (x) (= x 8)))) 7) (require (only-in n n)) n]))
            (term (blame n n (-- 7) (and/c (pred exact-nonnegative-integer? n) (pred (λ (x) (@ = x 8 n)) n)) (-- 7))))
 (test-->>p (term (annotator [(simple-module n (and/c exact-nonnegative-integer? (pred (λ (x) (= x 8)))) "7") (require (only-in n n)) n]))
            (term (blame n n (-- "7") (and/c (pred exact-nonnegative-integer? n) (pred (λ (x) (@ = x 8 n)) n)) (-- "7"))))
 (test-->>p fit-example (term (-- (pred string? rsa))))
 (test-->>p fit-example-keygen-string
            (term (blame keygen prime? (-- "Key") (pred exact-nonnegative-integer? prime?) (-- "Key"))))
 (test-->>p fit-example-rsa-7
            (term (-- (pred string? rsa)))
            (term (blame keygen keygen (-- (λ (x) 7)) (pred (prime? ^ keygen prime?) keygen) (-- 7))))
 (test-->>p example-8 (term (blame h g (-- #f) (pred (λ (x) x) g) (-- #f))))
 (test-->>p example-8-opaque 
            (term (-- (any/c)))
            (term (blame h g (-- (any/c)) (pred (λ (x) x) g) (-- (any/c)))))
 (test-->>p list-id-example (term (-- (cons (-- 1) 
                                            (-- (cons (-- 2) 
                                                      (-- (cons (-- 3) (-- empty))))))))) 
 (test-->>p (term (annotator ,list-rev-example-raw))
            (term (-- (cons (-- 3)
                            (-- (cons (-- 2)
                                      (-- (cons (-- 1)
                                                (-- empty)))))))))
 
 ;; Not sure about the remembered contracts in these examples. 
 (test-->>p (term (annotator [(simple-module n exact-nonnegative-integer? 5) (require (only-in n n)) n]))
            (term (-- 5))) 
 (test-->>p (term (annotator [(simple-module p
                          (cons/c exact-nonnegative-integer? exact-nonnegative-integer?)
                          (cons (-- 1) (-- 2)))
                        (require (only-in p p))
                        p]))
            (term (-- (cons (-- 1) (-- 2)) 
                      (cons/c (pred exact-nonnegative-integer? p) (pred exact-nonnegative-integer? p)))))
 (test-->>p (term (annotator [(simple-module p
                          (pred (λ (x) (if (cons? x)
                                           (= (first x)
                                              (rest x))
                                           #f)))
                          (cons (-- 1) (-- 1)))
                        (require (only-in p p))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (pred (λ (x) (if (@ cons? x p)
                                       (@ = 
                                          (@ first x p)
                                          (@ rest x p)
                                          p)
                                       #f))
                            p))))
 (test-->>p (term (annotator [(simple-module p
                          (and/c (cons/c exact-nonnegative-integer? exact-nonnegative-integer?)
                                 (pred (λ (x) (= (first x) (rest x)))))
                          (cons (-- 1) (-- 1)))
                        (require (only-in p p))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (cons/c (pred exact-nonnegative-integer? p) (pred exact-nonnegative-integer? p)) 
                      (pred (λ (x) (@ = (@ first x p) (@ rest x p) p)) p))))
 
 ;; Swap of and/c arguments above
 (test-->>p (term (annotator [(simple-module p
                          (and/c (pred (λ (x) (= (first x) (rest x))))
                                 (cons/c exact-nonnegative-integer? exact-nonnegative-integer?))                                
                          (cons (-- 1) (-- 1)))
                        (require (only-in p p))
                        p]))
            (term (-- (cons (-- 1) (-- 1))
                      (pred (λ (x) (@ = (@ first x p) (@ rest x p) p)) p)
                      (cons/c (pred exact-nonnegative-integer? p) (pred exact-nonnegative-integer? p)))))
 
 (test-->>p (term (annotator [(simple-module p
                          (cons/c exact-nonnegative-integer? exact-nonnegative-integer?)
                          (cons (-- 1) (-- 2)))
                        (require (only-in p p))
                        (first p)]))
            (term (-- 1)))
 (test-->>p (term (annotator [(simple-module p
                          (cons/c exact-nonnegative-integer? exact-nonnegative-integer?)
                          (cons (-- "hi") (-- 2)))
                        (require (only-in p p))
                        (first p)]))
            (term (blame p p (-- (cons (-- "hi") (-- 2))) (cons/c (pred exact-nonnegative-integer? p) (pred exact-nonnegative-integer? p)) (-- (cons (-- "hi") (-- 2))))))
 
 (test-->>p (term (annotator [(simple-module p
                          (cons/c (anything . -> . exact-nonnegative-integer?) anything)
                          (cons (-- (λ (x) "hi"))
                                (-- 7)))
                        (require (only-in p p))
                        ((first p) 7)]))
            (term (blame p p (-- (cons (-- (λ (x) "hi"))
                                       (-- 7)))
                         (pred exact-nonnegative-integer? p)
                         (-- "hi"))))
 
 
 (test-->>p (term [(simple-module mt-val (pred empty? mt-val) empty) 
                   (require (only-in mt-val mt-val))
                   (mt-val ^ † mt-val)])
            (term (-- empty)))
 
 (test-->>p list-id-example-contract
            (term (-- (cons (-- 1)
                            (-- (cons (-- 2)
                                      (-- (cons (-- 3)
                                                (-- empty))))))
                      ,list-of-nat/c)))
 )

(define fact-prog
  (term ((simple-module fact (exact-nonnegative-integer? . -> . exact-nonnegative-integer?)
           (λ f (x) (if (= x 0) 1 (* x (f (sub1 x))))))
         (simple-module input exact-nonnegative-integer? ☁)
         (require (only-in input input) (only-in fact fact))
         (fact input))))

(define wrong-prog
  (term ((simple-module fact (exact-nonnegative-integer? . -> . exact-nonnegative-integer?)
           (λ f (x) (if (= (add1 x) (add1 0)) 1 (* x (f (sub1 x))))))
         (simple-module input exact-nonnegative-integer? ☁)
         (require (only-in input input) (only-in fact fact))
         (fact input))))

(define fit-ex-prog
  (term ((simple-module prime? (anything . -> . boolean?) ☁)
         (simple-module keygen (anything . -> . (pred prime?)) ☁) 
         (simple-module rsa ((pred prime?) . -> . (string? . -> . string?)) ☁)
         (require (only-in keygen keygen) (only-in rsa rsa))
         ((rsa (keygen #f)) "Plain"))))

(define (final P)
  (apply-reduction-relation* (stepΔ-gc (program-modules P))
                             (term (load ,(last P)))
                             #:cache-all? #t))
#;#;
(define next #f)
(define result #f)
#;
(define (single P)
  (set! next (λ () 
               (define r (append-map (λ (p) (apply-reduction-relation (stepΔ-gc (program-modules P)) p)) result))
               (set! result r)
               r))
  (let ([r (apply-reduction-relation (stepΔ-gc (program-modules P))
                                     (term (load ,(last P))))])
    (set! result r)
    r))
