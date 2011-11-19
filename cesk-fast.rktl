#lang racket
(require (except-in redex/reduction-semantics plug) (for-syntax syntax/parse) (prefix-in c: racket/contract))
(require (except-in "lang.rkt" final-state?) "flat-check.rkt" "meta.rkt" "alpha.rkt" "util.rkt" "annotate.rkt" "examples.rkt" 
         (only-in "step.rkt" lookup-modref/val lookup-modref/con) (prefix-in s: "step.rkt"))
(require (prefix-in ce: "cesk.rkt") (only-in racket/match ==))
(provide (except-out (all-defined-out) test))
(test-suite test cesk)

;; FIXME handling of cons, car, cdr is broken on pairs of functions.

(current-cache-all? #t)

;; turns of contract checking
(define-syntax-rule (define/contract a b c) (define a c))

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
   
  (ρ (side-condition any_1 (hash? (term any_1))))
  (clo (V ρ))
  (D clo K)
  (Ds (side-condition any_1 (set? (term any_1))))
  (σ (side-condition any_1 ((hash/c c:any/c (set/c D?) #:flat? #t) (term any_1))))
  (ς (E ρ σ K)))


(define-metafunction CESK*
  widen : o V-or-B -> V-or-B
  [(widen o B) B]
  [(widen o V) 
   V
   (side-condition (current-exact?))]
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

(define (alloc-addr σ vals)
   (cond [(current-exact?) (variables-not-in* (hash-keys σ) vals)]
         [(andmap symbol? vals) 
          
          (variables-not-in (hash-keys σ) vals)
          #;vals]
         [(andmap V? vals) 
          (build-list (length vals) values)
          (variables-not-in* (hash-keys σ) vals)]
         [else ;; continuations
          (map (λ (p) (if (list? p) (drop-right p 1) p)) vals)]))

(define (alloc σ vals)
  (for/list ([a (alloc-addr σ vals)])
    `(loc ,a)))

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


(define (extend-env ρ xs as)
  (for/fold ([ρ ρ]) ([x (in-list xs)] [a (in-list as)])
    (hash-set ρ x a)))

(define D? (redex-match CESK* D))

(define addr? (redex-match CESK* a))

(define/contract (extend-sto1 s a d)
  (hash? addr? D? . -> . hash?)
  (hash-update s a (λ (e) (set-add e d)) (set)))

(define/contract (extend-sto σ as ds)
  (hash? (listof addr?) (c:listof D?) . -> . hash?)
  (for/fold ([σ σ]) ([a (in-list as)] [d (in-list ds)])
    (extend-sto1 σ a d)))



(define/contract (sto-lookup a b) (hash? addr? . -> . (c:listof D?))
  (set->list (hash-ref a b)))

(define (env-lookup e x) (hash-ref e x))

(define-metafunction CESK*
  load : any -> any
  [(load any)
   ,(st (term any) #hash() #hash() 'MT)])

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
  unload : any -> E
  [(unload (side-condition any_1 (st? (term any_1))))
   ,(st-c (term any_1))]
  [(unload (E ρ σ MT))
   E]
  [(unload (E ρ σ K))
   (unload ((plug E K) ρ σ K_1))
   (where {D_0 ... K_1 D_1 ...} ,(sto-lookup (term σ) (term (addr-of K))))])

(define-struct/contract st ([c (flat-named-contract 'E (redex-match CESK* E))] 
                            [e (hash/c symbol? c:any/c)]
                            [s (hash/c c:any/c set?)] 
                            [k (flat-named-contract 'K (redex-match CESK* K))])
  #:transparent)
(define-struct results (vs) #:transparent)
;(define-struct S (name results) #:transparent)

(define (S n rs)
  (results (for/list ([r rs]) (list n r))))

(define state? st?)


(define V? (redex-match CESK* V))
(define AV? (redex-match CESK* AV))
(define AE? (redex-match CESK* AE))

(define-match-expander V:
  (syntax-parser
   [(_ pat) #'(? V? pat)]))

(define (combine-S . ss)
  (match ss
    [(list (results vs) ...)
     (results (apply append vs))]))

(define-syntax-rule (choose [tst . rhs] ...)
  (apply combine-S
         (filter values (list (and tst (let () . rhs)) ...))))

(define (step* state)
  (match state    
    [(st (? AE? (cons '-- (list-no-order `(or/c ,C1 ...) C ...))) ρ σ K) 
     (S 'or-split
        (for/list ([c C1])
          (st (term (remember-contract (-- (any/c) ,@C) ,c)) ρ σ K)))]
    
    [(st (? AE? (cons '-- (list-no-order `(rec/c ,x ,body) C ...))) ρ σ K)
     (S 'rec-unroll
        (list (st (term (remember-contract (-- (any/c) ,@C) (unroll (rec/c ,x ,body))))
                  ρ σ K)))]
    
    [(st (V: V) ρ σ `(AP ,clo ((,E_0 ,ρ_0) ,rest ...) ,ℓ ,a))
     (S 'ap-next
        (list (st E_0 ρ_0 σ `(AP (,@clo (,V ,ρ)) ,rest ,ℓ ,a))))]
    [(st (V: V) ρ σ `(OP ,o ,clo (,E_0 ,rest ...) ,ρ_0 ,ℓ ,a))
     (S 'op-next
        (list (st E_0 ρ_0 σ `(OP ,o (,@clo (,V ,ρ)) ,rest ,ρ_0 ,ℓ ,a))))]
    
    [(st `(@ ,(? (redex-match CESK* op) op) ,E_0 ,E_1 ... ,ℓ) ρ σ K)
     (S 'op-push
        (for/list ([a (alloc σ (list K))])
          (define σ_0 (extend-sto1 σ a K))
          (st E_0 ρ σ_0 `(OP ,op () ,E_1 ,ρ ,ℓ ,a))))]
    
    [(st `(@ ,E_0 ,E_1 ... ,ℓ) ρ σ K)
     (S 'ap-push
        (for/list ([a (alloc σ (list K))])
          (define σ_0 (extend-sto1 σ a K))
          (st E_0 ρ σ_0 `(AP () ,(map (λ (e) (list e ρ)) E_1) ,ℓ ,a))))]
    
    [(st `(if ,E_0 ,E_1 ,E_2) ρ σ K)
     (S 'if-push
        (for/list ([a (alloc σ (list K))])
          (define σ_0 (extend-sto1 σ a K))
          (st E_0 ρ σ_0 `(IF ,E_1 ,E_2 ,ρ ,a))))]
    
    
    ;; begin
   [(st (V: V) ρ σ `(BEG (,E ,ρ_0) ,a))
    (S 'begin-done
       (for/list ([K (sto-lookup σ a)])
         (st E ρ_0 σ K)))]      
   
   ;; let
    [(st (V: V) ρ σ `(LET . ,_)) (error "let is broken in the machine")]
    
    [(st (? (redex-match CESK* x) x) ρ σ K)
     (S 'var
        (for/list ([D (sto-lookup σ (env-lookup ρ x))])
          (match D
            [(list V ρ_0) (st V ρ_0 σ K)])))]
    [(st (? (redex-match CESK* PV) pv) ρ σ K)
     (S 'wrap (list (st `(-- ,pv) ρ σ K)))]
    
    ;; nullary application
    [(st (V: V-proc) ρ σ `(AP () () ,ℓ ,a))
     (match V-proc
       [`(-- (λ () ,E) ,C ...)
        (S 'β-0 
           (for/list ([K (sto-lookup σ a)])
             (st E ρ σ K)))]
       [(and fun `(-- (λ ,rec () ,E) ,C ...))
        (S 'β-rec-0 
           (for*/list ([K (sto-lookup σ a)]
                       [a_1 (alloc σ (list rec))])
             (st E 
                 (extend-env ρ (list rec) (list a_1))
                 (extend-sto1 σ a_1 (list fun ρ))
                 K)))]
       ;; these next two cases are identical
       [`((--> (λ () ,C)) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_f))
        (S 'nullary-blessed-β-dep
           (for/list ([clo (sto-lookup σ a_f)])
             (match-let* ([K `(CHK ,C ,ρ ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]
                          [`(,V_f ,ρ_f) clo]
                          [`(,a_k) (alloc σ (list K))]
                          [σ_1 (extend-sto1 σ a_k K)])
               (st V_f ρ_f σ_1 `(AP () () ,ℓ ,a_k)))))]
       [`((--> ,C) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_f))
        (S 'nullary-blessed-β
           (for/list ([clo (sto-lookup σ a_f)])
             (match-let* ([K `(CHK ,C ,ρ ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]
                          [`(,V_f ,ρ_f) clo]
                          [`(,a_k) (alloc σ (list K))]
                          [σ_1 (extend-sto1 σ a_k K)])
               (st V_f ρ_f σ_1 `(AP () () ,ℓ ,a_k)))))]
       [_ 
        (choose [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
                      (or (equal? 0 (term (arity ,V-proc)))
                          (not (term (arity ,V-proc))))
                      (redex-match CESK* AV V-proc))
                 (S 'apply-abs0
                    (for/list ([K (sto-lookup σ a)])
                      (match-let* ([`(-- ,C ...) V-proc]
                                   [C_0 (term (range-contracts ,C ()))])
                        (st (term (remember-contract (-- (any/c)) ,@(for/list ([c C_0])
                                                                      (term (try-close-contract ,c ,ρ ,σ)))))
                            '#hash() σ K))))]
                [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
                      (not (equal? 0 (term (arity ,V-proc)))))
                 (S 'blame-arity
                    (for/list ([K (sto-lookup σ a)])
                      (st `(blame ,ℓ  Λ ,V-proc λ ,V-proc) ρ σ K)))]                
                [(and (term (∈ #f (δ (@ procedure? ,V-proc ★)))))
                 (S 'blame-not-proc
                    (for/list ([K (sto-lookup σ a)])
                      (st `(blame ,ℓ  Λ ,V-proc λ ,V-proc) ρ σ K)))])])]
    
    ;; unary+ application
    [(st (V: V) ρ σ `(AP ((,(V: V-proc) ,ρ_0) ,clo ...) () ,ℓ ,a))
     (choose 
       [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
             (equal? (add1 (length clo))
                     (term (arity ,V-proc))))
        (match V-proc
          [`(-- (λ ,rec (,x ...) ,E) ,C ...)
           (define a1s (alloc σ (cons rec x)))
           (S 'β-rec
              (for/list ([K (sto-lookup σ a)])
                (st E 
                    (extend-env ρ_0 (cons rec x) a1s)
                    (extend-sto σ a1s (cons `((-- (λ ,rec ,x ,E) ,@C) ,ρ_0)
                                            (append clo (list (list V ρ)))))
                    K)))]
          [`(-- (λ (,x ...) ,E) ,C ...)
           (define a1s (alloc σ x))
           (S 'β
              (for/list ([K (sto-lookup σ a)])
                (st E 
                    (extend-env ρ_0 x a1s)
                    (extend-sto σ a1s (append clo (list (list V ρ))))
                    K)))]          
          [`((,C_0 ... --> (λ (,x ...) ,C_1)) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_f))
           (match-let* ([a_1 (alloc σ x)]
                        (ρ_3 (extend-env ρ x a_1))
                        [K `(CHK ,C_1 ,ρ_3 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]
                        [(list (and clo2 (list V_2 ρ_2)) ...) (cons (list V ρ) (reverse clo))] ;; FIXME -- is this reverse right?
                        [(list a_k) (alloc σ (list K))]
                        [K2 `(AP ()
                                 ,(for/list ([c C_0]
                                             [v V_2]
                                             [ρ ρ_2])
                                    `((,c <= ,ℓ_2 ,ℓ_1 ,v ,ℓ_3 ,v) ,ρ))
                                 ,ℓ ,a_k)]
                        [σ_1 (extend-sto σ (cons a_k a_1) (cons K clo2))])
             (S 'unary+-blessed-β-dep
                (for/list ([clo_1 (sto-lookup σ a_f)])
                  (match-define (list V_f ρ_f) clo_1)
                  (st V_f ρ_f σ_1 K2))))]
          [`((,C_0 ... --> ,C_1) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_f))
           ;(printf "got here \n")
           (match-let* ([K `(CHK ,C_1 ,ρ ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]
                        [(list a_k) (alloc σ (list K))]
                        [σ_1 (extend-sto1 σ a_k K)]
                        [K2 `(AP ()
                                 ,(for/list ([clo_1 (cons (list V ρ) clo)]
                                             [C_0* C_0])
                                    (match-let ([(list V_2 ρ_2) clo_1])
                                      `((,C_0* <= ,ℓ_2 ,ℓ_1 ,V_2 ,ℓ_3 ,V_2) ,ρ_2)))
                                 ,ℓ ,a_k)])
             (S 'unary+-blessed-β
                (for/list ([clo_1 (sto-lookup σ a_f)])
                  (match-define (list V_f ρ_f) clo_1)
                  (st V_f ρ_f σ_1 K2))))]
          [`(-- ,C ...) 
           (S 'apply-abs-known-arity
              (match-let ([dom-con (term (domain-contracts ,C))])
                (for/list ([clo_1 `((,V ,ρ) . ,clo)]
                           [C_demon (for/list ([C_D dom-con]) (term (∧ . ,C_D)))])
                  (match-let* ([`(,U ,ρ_2) clo_1]
                               [(list (list V_0 ρ_0) ...) (append clo (list (list V ρ)))]
                               ;; FIXME, closing contracts in their environments
                               ;; because we don't have contract closures.
                               [V_0c (for/list ([v V_0] [ρ ρ_0]) 
                                       (term (try-close-value ,v ,ρ ,σ)))]
                               [C_0 (for/list ([C_0 (term (range-contracts ,C ,V_0c))]
                                               [ρ ρ_0])
                                      (term (try-close-contract ,C_0 ,ρ ,σ)))]
                               [E_result (term (remember-contract (-- (any/c)) ,@C_0))])                    
                    (st (term (amb (-- 0) (demonic* ,C_demon ,U))) ρ_2 σ `(BEG (,E_result #hash()) ,a))))))])]
       [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
             (not (term (arity ,V-proc))))
        (S 'apply-abs-no-arity
           (for/list ([clo* (cons (list V ρ) clo)])
             (match-define `(,U ,ρ_2) clo*)
             (st (term (amb (-- 0) (demonic* (any/c) ,U))) ρ_2 σ (term (BEG ((-- (any/c)) #hash()) ,a)))))]
       [(and (term (∈ #t (δ (@ procedure? ,V-proc ★))))
             (not (equal? (add1 (length clo))
                          (term (arity ,V-proc)))))
        (S 'blame-arity
           (for/list ([K (sto-lookup σ a)])
             (st `(blame ,ℓ  Λ ,V-proc λ ,V-proc) ρ_0 σ K)))]
       [(term (∈ #f (δ (@ procedure? ,V-proc ★)))) 
        (S 'blame-not-proc
           (for/list ([K (sto-lookup σ a)])
             (st `(blame ,ℓ  Λ ,V-proc λ ,V-proc) ρ_0 σ K)))])]

    
    
    [(st (V: V) ρ σ `(IF ,E_1 ,E_2 ,ρ_1 ,a))     
     (S 'if
        (for*/list ([K (sto-lookup σ a)]
                    [r (term (δ (@ false? ,V ★)))]
                    [r* (in-value (match r [`(-- ,(? boolean? a)) a] [else 0]))]
                    #:when (boolean? r*))
          (st (if (not r*) E_1 E_2) ρ_1 σ K)))]
    ;; δ
   ;; FIXME broken delta rule for things producing closures.
    [(st (V: V) ρ σ `(OP ,op ,(list (list V_0 ρ_0) ...) () ,ρ_1 ,ℓ ,a))
     (S 'δ
        (for*/list ([K (sto-lookup σ a)]
                    [V-or-B (term (δ ,`(@ ,op ,@V_0 ,V ,ℓ)))])
          (st (term (widen ,op ,V-or-B)) '#hash() σ K)))]
    
    [(st `(begin ,E_0 ,E_1) ρ σ K)
     (S 'beg-push
        (match-let ([(list a) (alloc σ (list K))])
          (define σ_0 (extend-sto1 σ a K))
          (list (st E_0 ρ σ_0 `(BEG (,E_1 ,ρ) ,a)))))]
    
    [(st `(let ,x ,E_0 ,E_1) ρ σ K)
     (S 'let-push
        (match-let ([(list a) (alloc σ (list K))])
          (define σ_0 (extend-sto1 σ a K))
          (list (st E_0 ρ σ_0 `(LET ,x ,E_1 ,ρ ,a)))))]
    
    
    [(st (V: V) ρ σ `(CHK (,C ... -> ,result) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (choose
      [(term (∈ #t (δ (@ procedure? ,V ★))))
       (S 'chk-fun-pass
        (match-let* ([(list a_new) (alloc σ (list V))]
                     [σ_1 (extend-sto1 σ a_new `(,V ,ρ))])
          (for/list ([K (sto-lookup σ a)])
            (st `((,@C --> ,result) <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 (addr ,a_new)) ρ_1 σ_1 K))))]
      [(term (∈ #f (δ (@ procedure? ,V ★))))
       (S 'chk-fun-fail-fail
          (for/list ([K (sto-lookup σ a)])
            (st `(blame ,ℓ_1 ,ℓ_3 ,V-or-AE (,@C -> ,result) ,V) ρ σ K)))])]
    
    
    
    [(st (V: V) ρ σ `(CHK ,(? (redex-match CESK* FLAT) FLAT) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (match-let* ([K
                   `(IF ,(term (remember-contract ,V (try-close-contract ,FLAT ,ρ_1 ,σ)))
                       (blame ,ℓ_1 ,ℓ_3 ,V-or-AE ,FLAT ,V)
                       ,ρ ,a)]
                  [(list a_k) (alloc σ (list K))]
                  [σ_new (extend-sto1 σ a_k K)])
       (S 'flat-check
          (list (st V ρ σ_new
                    `(AP (((-- ,(term (flat-check ,FLAT ,V))) ,ρ_1)) () Λ ,a_k)))))]
    
    [(st (V: V) ρ σ `(CHK (rec/c ,X ,HOC) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (S 'chk-unroll
        (list (st V ρ σ `(CHK ,(term (unroll (rec/c ,X ,HOC))) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))))]
    
    [(st (V: V) ρ σ `(CHK (or/c ,FLAT ,HOC) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (match-let* ([K `(CHK-OR ,V ,ρ (or/c ,FLAT ,HOC) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]                   
                  [(list a_k) (alloc σ (list K))]
                  [σ_new (extend-sto1 σ a_k K)])
       (S 'check-or-pass
        (list
         (st V ρ σ_new
             `(AP (((-- ,(term (flat-check ,FLAT ,V))) ,ρ_1)) () Λ ,a_k)))))]
   
   [(st (V: V) ρ_0 σ `(CHK-OR ,U ,ρ (or/c ,FLAT ,HOC) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
    (choose 
     [(term (∈ #t (δ (@ false? ,V Λ))))
      (S 'check-or-false (list (st U ρ σ `(CHK ,HOC ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))))]
     [(term (∈ #f (δ (@ false? ,V Λ))))
      (S 'check-or-true
         (for/list ([K (sto-lookup σ a)])
           (st (term (remember-contract ,U (try-close-contract ,FLAT ,ρ_1 ,σ))) ρ σ K)))])]
    
    [(st (V: V) ρ σ `(CHK (and/c ,C_0 ,C_1) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (match-let* ([K `(CHK ,C_1 ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)]                   
                  [(list a_k) (alloc σ (list K))]
                  [σ_1 (extend-sto1 σ a_k K)])
       (S 'check-and-push 
          (list (st V ρ σ_1 `(CHK ,C_0 ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a_k)))))]
   
    [(st `(-- (cons ,V_0 ,V_1) ,C ...) ρ σ `(CHK (cons/c ,C_0 ,C_1) ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a))
     (match-let* ([K `(CHK-CONS ,C_1 ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,V_1 ,ρ ,a)]                   
                  [(list a_k) (alloc σ (list K))]
                  [σ_new (extend-sto1 σ a_k K)])
       (S 'check-cons-pass-first 
          (list (st V_0 ρ σ_new `(CHK ,C_0 ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a_k)))))]
   
    [(st (V: V) ρ σ `(CHK-CONS ,C_1 ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,V_1 ,ρ_2 ,a))
     (match-let* ([K `(OP cons ((,V ,ρ)) () #hash() Λ ,a)]
                  [(list a_k) (alloc σ (list K))]
                  [σ_new (extend-sto1 σ a_k K)])
     (S 'check-cons-pass-rest
        (list (st V_1 ρ_2 σ_new `(CHK ,C_1 ,ρ_1 ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a_k)))))]
    
    
    [(st `(,C <= ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,(? (redex-match CESK* E) E)) ρ σ K)
     (match-let* ([`(,a) (alloc σ (list K))]
                  [σ_0 (extend-sto1 σ a K)])       
       (S 'chk-push 
          (list (st E ρ σ_0
                    `(CHK ,C ,ρ ,ℓ_1 ,ℓ_2 ,V-or-AE ,ℓ_3 ,a)))))]        
        
    [a (S #f null)]))

(define (factorial n)
  (if (zero? n) 1 (* n (factorial (sub1 n)))))

(define (st->list s)
  (match s
    [(st a b c d) (list a b c d)]))

(define/contract ((step∆ Ms) s)
  (c:any/c . -> . (state? . -> . (struct/c S (or/c #f symbol?) (listof state?))))
  (match s 
    [(st `(,f_1 ^ ,f ,f) ρ σ K)
     (S 'Δ-self
        (list (st (term (-- (lookup-modref/val ,f ,f_1 ,Ms))) ρ σ K)))]
    [(st `(,f_1 ^ ,ℓ ,f) ρ σ K)
     (define V (term (lookup-modref/val ,f ,f_1 ,Ms)))
     (define C (term (lookup-modref/con ,f ,f_1 ,Ms)))     
     (cond [(redex-match CESK* bullet V)
            (S '∆-opaque 
               (list
                (st (term (,C <= ,f ,ℓ (-- ,C) ,f_1 (remember-contract (-- (any/c)) ,C)))
                    ρ σ K)))]
           [else
            (S '∆-other
               (list (st (term (,C <= ,f ,ℓ (-- ,V) ,f_1 (-- ,V)))
                         ρ σ K)))])]
    [(st (? (redex-match CESK* B) b) ρ σ (and (not 'MT) K))
     (S 'halt-blame (list (st b '#hash() (term (gc (,b #hash() ,σ MT))) 'MT)))]
    [_ (step* s)]))


(define-metafunction CESK*
  restrict : any (any ...) -> any
  [(restrict any_l any_keys)
   ,(for/hash ([(k v) (in-hash (term any_l))]
               #:when (member k (term any_keys)))
      (values k v))])

(define-metafunction CESK*
  live-loc-clo : (E ρ) -> (a ...)
  [(live-loc-clo (E ρ))
   (a_0 ... a_1 ...)
   (where (a_0 ...) (live-loc-E E))
   (where (a_1 ...) (live-loc-env (restrict ρ (fv E))))])

(define-metafunction CESK*
  live-loc-env : ρ -> (a ...)
  [(live-loc-env ρ)
   ,(hash-values (term ρ))])


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

#;
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

(define-metafunction CESK*
  live-loc-Ds : any -> (a ...)
  [(live-loc-Ds any_d)
   ,(apply append
           (for/list ([d (term any_d)])
             (match d
               [`(,V ,ρ) (term (live-loc-clo (,V ,ρ)))]
               [K (term (live-loc-K ,K))])))])

(define-metafunction CESK*
  reachable : (a ...) (a ...) σ -> (a ...)
  [(reachable () (a ...) σ) (a ...)]
  [(reachable (a a_0 ...) (a_1 ...) σ)   
   (reachable (set-minus (a_0 ... a_2 ...) (a a_1 ...))
              (a a_1 ...)
              σ)
   (where (a_2 ...) (live-loc-Ds ,(sto-lookup (term σ) (term a))))])

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


(define (step∆-gc-R Ms)
  (define step (step∆ Ms))
  (reduction-relation 
   CESK*
   [--> any_old ,(st (term E) (term ρ_1) (term σ_1) (term K))
        (where (any_1 ... (any_name any_state) any_2 ...)
               ,(results-vs (step (term any_old))))
        (where (E ρ σ K) ,(st->list (term any_state)))
        (where σ_1 (gc (E ρ σ K)))
        (where ρ_1 (restrict ρ (fv E)))
        (computed-name (term any_name))]))

(define (step∆-gc Ms)
  (define step (step∆ Ms))
  (λ (s)
    (results
     (for/list ([r (results-vs (step s))])
       (match-define (st E ρ σ K) (second r))
       (define σ_1 (term (gc ,(list E ρ σ K))))
       (define ρ_1 (term (restrict ,ρ (fv ,E))))
       (list (first r) (st E ρ_1 σ_1 K))))))

(define step-gc-R (step∆-gc-R null))

(define (final-state? s)
  (and (eq? 'MT (st-k s))
       (or (redex-match CESK* V (st-c s))
           (redex-match CESK* B (st-c s)))))


(define ((colorize Ms) x node)
  (define opaques (filter-map (λ (M) (match M
                                       [(list 'module n lang (list 'define _ ☁) ... prov) n]
                                       [_ #f]))
                              Ms))
  (define x* (if (st? x) (st->list x) x))
  (cond [(redex-match CESK* (V any any_1 MT) x*) "green"]
        [(redex-match CESK* (B any any_1 MT) x*)
         (redex-let CESK*
                    ([(blame ℓ ℓ_0 V any V_0) (car x*)])
                    (cond [(equal? (term ℓ) '★) "pink"]
                          [(member (term ℓ) opaques) "pink"]
                          [else "red"]))]
        [(null? (term-node-children node)) "blue"]
        [else #t]))

(define-syntax-rule (trace-it P . rest)
  (traces (step∆-gc-R (program-modules P))
          (term (load ,(last P)))
          #:pred (colorize (program-modules P))
          . rest))

(define-syntax-rule (step-it P . rest)
  (stepper (step∆-gc-R (program-modules P))
           (term (load ,(last P)))))



(define (step-fixpoint P)
  (define l (term (load ,(last P))))
  (define f (step∆-gc (program-modules P)))
  (let loop ([terms (list l)] [finals (set)] [seen (set)] [iters 0])
    (when (= 0 (modulo iters 10))
      (printf "~a iterations, ~a terms seen, ~a frontier, ~a elapsed ms\n" iters (set-count seen) (length terms) 
              (current-process-milliseconds)))
    (define rs (for/list ([t (in-list terms)])
                 (list t (map second (results-vs (f t))))))
    (define-values
      (new-seen new-finals new-terms)
      (for/fold ([s seen] [f finals] [new-terms (list)])
        ([r (in-list rs)])
        (values (set-union s (list->set (second r)))
                (if (null? (second r))
                    (set-add f (first r))
                    f)
                (append new-terms
                        (filter-not (λ (e) (set-member? s e)) (second r))))))
    ;(printf "new-seen: ~a\nnew-terms: ~a\n" (set-count new-seen) (length new-terms))
    (cond [(empty? new-terms)
           (printf "~a iterations, ~a terms seen, ~a frontier, ~a elapsed ms\n" iters (set-count seen) (length terms) 
                   (current-process-milliseconds))
           (remove-duplicates (for/list ([f new-finals]) f))]
          [else             
           (loop (remove-duplicates new-terms) new-finals new-seen (add1 iters))])))

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
  (test-->>E (step∆-gc-R (program-modules P))
            ;#:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2))))
            ;#:cycles-ok
            (term (load ,(last P)))
            (term (load ,e))) ...))

(define-syntax-rule (test-->>pE P e ...)
  (test-->>E (step∆-gc-R (program-modules P))
             #;#;
             #:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2))))
             (term (load ,(last P)))
             (term (load ,e)) ...))

(define-syntax-rule (test-->>c r t1 t2)
  (begin
    (print-here r)
    (test-->> r #:equiv (λ (e1 e2) (term (≡α (unload ,e1) (unload ,e2)))) (term (load ,t1)) (term (load ,t2)))))

(test
 (test-->>c step-gc-R (term (@ (-- (λ (x) 0)) (-- 1) †)) (term (-- 0)))
 #; ;; this loops
 (test-->>c v 
            (term (@ (-- (λ f (x) (@ f x †))) (-- 0) †))
            (term (@ (-- (λ f (x) (@ f x †))) (-- 0) †))) 
 
 (test-->>c step-gc-R (term (@ (-- 0) (-- 1) †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test-->>c step-gc-R (term (if (-- 0) 1 2)) (term (-- 1)))
 (test-->>c step-gc-R (term (if (-- #t) 1 2)) (term (-- 1)))
 (test-->>c step-gc-R (term (if (-- #f) 1 2)) (term (-- 2)))
 (test-->>c step-gc-R (term (@ add1 (-- 0) †)) (term (-- 1)))
 (test-->>c step-gc-R (term (@ procedure? (-- #f) †)) (term (-- #f)))
 (test-->>c step-gc-R (term (@ procedure? (-- (λ (x) x)) †)) (term (-- #t)))
 (test-->>c step-gc-R (term (@ procedure? (-- (λ f (x) x)) †)) (term (-- #t)))
 (test-->>c step-gc-R (term (@ procedure? (-- ((any/c) -> (any/c))) †)) (term (-- #t)))
 (test-->>c step-gc-R (term (@ cons (-- 1) (-- 2) †)) (term (-- (cons (-- 1) (-- 2)))))
 
 (test-->>c step-gc-R (term (@ (λ (x) 0) 1 †)) (term (-- 0)))                
 (test-->>c step-gc-R (term (@ 0 1 †)) (term (blame † Λ (-- 0) λ (-- 0))))
 (test-->>c step-gc-R (term (if 0 1 2)) (term (-- 1)))
 (test-->>c step-gc-R (term (if #t 1 2)) (term (-- 1)))
 (test-->>c step-gc-R (term (if #f 1 2)) (term (-- 2)))
 (test-->>c step-gc-R (term (@ add1 0 †))  (term (-- 1)))
 (test-->>c step-gc-R (term (@ procedure? #f †)) (term (-- #f)))
 (test-->>c step-gc-R (term (@ cons 1 2 †)) (term (-- (cons (-- 1) (-- 2)))))
 (test-->>c step-gc-R (term (@ ((and/c (any/c) ((any/c) -> (any/c))) <= f g (-- 0) f (-- (λ (x) x)))
                               5 h))
            (term (-- 5))))


(test
 (test-->>c step-gc-R (term (@ (λ () 4) f)) (term (-- 4)))
 (test-->>c step-gc-R (term (@ (λ z () 4) f)) (term (-- 4)))
 (test-->>c step-gc-R (term (@ (-- (-> (nat/c))) f)) (term (-- (nat/c))))
 (test-->>c step-gc-R (term ((nat/c) <= f g (-- 0) f (-- 5))) (term (-- 5)))
 (test-->>c step-gc-R 
            (term ((nat/c) <= f g (-- 0) f (-- (λ (x) x))))
            (term (blame f f (-- 0) (nat/c) (-- (λ (x) x)))))
 (test-->>c step-gc-R 
            (term ((nat/c) <= f g (-- 0) f (-- #t))) 
            (term (blame f f (-- 0) (nat/c) (-- #t))))
 (test-->>c step-gc-R 
            (term (((any/c)  -> (any/c)) <= f g (-- 0) f (-- (λ (x) x))))
            ;; kind of a giant hack
            (term (((any/c) --> (any/c)) <= f g (-- 0) f (addr ,(car (alloc (hash '(loc 0) (set '((-- 0) #hash()))) `((-- (λ (x) x)))))))))
 (test-->>c step-gc-R 
            (term (((any/c)  -> (any/c)) <= f g (-- 0) f (-- 5)))
            (term (blame f f (-- 0) ((any/c) -> (any/c)) (-- 5))))
 (test-->>c step-gc-R
            (term ((pred (λ (x) 0) ℓ) <= f g (-- 0) f (-- 5)))
            (term (-- 5 (pred (λ (x) 0) ℓ))))
 (test-->>c step-gc-R
            (term (begin 3 4))
            (term (-- 4)))
 (test-->>c step-gc-R
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
 (test-->>p (term (annotator [(simple-module p (rec/c X (or/c empty? (cons/c anything X))) ☁)
                        (require (only-in p p))
                        p]))
            (term (-- (pred empty? p))))
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
                                             (or/c exact-nonnegative-integer? (anything . -> . anything))
                                             1)
                              (require p)
                              (add1 p)]))
            (term (-- 2)))
 (test-->>p (term (annotator [(simple-module p
                                             (-> (λ () anything))
                                             (λ () 1))
                              (require p)
                              (p)]))
            (term (-- 1)))
 (test-->>p (term (annotator [(simple-module p
                                             (exact-nonnegative-integer? . -> . (λ (x) (pred (λ (z) (= x z)))))
                                             (λ (q) q))
                              (require p)
                              (p 5)]))
            (term (-- 5)))
 (test-equal (not (redex-match CESK* B 
                               (st-c (first 
                                      (step-fixpoint (term (annotator [(simple-module p
                                                                                      (-> (λ () anything))
                                                                                      (λ () 1))
                                                                       (require p)
                                                                       (p 1)])))))))
             #f)
 
 (test-->>p (term (annotator [(simple-module p
                                             anything
                                             •)
                              (require p)
                              (p 1)]))
            (term (-- (any/c))))
 (test-->>p (term (annotator [(simple-module p
                                             anything
                                             •)
                              (require p)
                              (p)]))
            (term (-- (any/c))))
 (test-->>p (term (annotator [(simple-module p anything 1)
                              (require p)
                              (p 2)]))
            (term (blame † Λ (-- 1) λ (-- 1))))
 
 (test-->>p (term (annotator [(simple-module p anything (λ (x y) x))
                              (require p)
                              (p 1)]))
            (term (blame † Λ (-- (λ (x y) x)) λ (-- (λ (x y) x)))))
 (test-->>p (term (annotator [(simple-module p anything (λ () x))
                              (require p)
                              (p 1)]))
            (term (blame † Λ (-- (λ () x)) λ (-- (λ () x)))))
 (test-->>p (term (annotator [(simple-module p
                                             (or/c exact-nonnegative-integer? (anything . -> . anything) )
                                             (λ (x) x))
                              (require p)
                              (p 2)]))
            (term (-- 2)))
 
 (test-->>p (term (annotator [(simple-module p
                                             (rec/c X (anything . -> . anything) )
                                             (λ (x) x))
                              (require p)
                              (p 2)]))
            (term (-- 2)))
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
         (module keygen racket (require prime?) (provide/contract [keygen (anything . -> . (pred prime?))])) 
         (module rsa racket (require prime?) (provide/contract [rsa ((pred prime?) . -> . (string? . -> . string?))]))
         (require keygen rsa)
         ((rsa (keygen #f)) "Plain"))))

(define fit-ex-prog2
  (term ((simple-module prime? (anything . -> . boolean?) ☁)
         (module keygen racket (require prime?) (provide/contract [keygen (-> (pred prime?))]))
         (module rsa racket (require prime?) (provide/contract [rsa ((pred prime?) . -> . (string? . -> . string?))]))
         (require keygen rsa)
         ((rsa (keygen)) "Plain"))))

(test
 (test-equal (step-fixpoint (term (annotator ,fit-ex-prog)))
             (list (st '(-- (pred string? rsa)) '#hash() '#hash() 'MT)))
 (test-equal (step-fixpoint (term (annotator ,fit-ex-prog2)))
             (list (st '(-- (pred string? rsa)) '#hash() '#hash() 'MT))))

(define (final P)
  (apply-reduction-relation* (step∆-gc-R (program-modules P))
                             (term (load ,(last P)))
                             #:cache-all? #t))
#;#;
(define next #f)
(define result #f)
#;
(define (single P)
  (set! next (λ () 
               (define r (append-map (λ (p) (apply-reduction-relation (step∆-gc (program-modules P)) p)) result))
               (set! result r)
               r))
  (let ([r (apply-reduction-relation (step∆-gc (program-modules P))
                                     (term (load ,(last P))))])
    (set! result r)
    r))
