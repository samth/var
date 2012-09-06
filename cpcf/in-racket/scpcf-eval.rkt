#lang racket

(require rackunit)
(require racket/contract)
(require "scpcf-lang.rkt")
(require "env.rkt")

(provide
 (contract-out
  [load (prog? . -> . cek?)]
  [step (cek? . -> . (set/c cek?))]
  [eval-cek (s-exp? . -> . (set/c eval-answer?))]
  
  [eval-answer? (any/c . -> . boolean?)]))

;; CEK = (cek [Listof Module] Closure Kont)
(struct cek (ms clo kont) #:transparent)

;; Kont = Mt
;;      | Ap [Listof ValClosure] [Listof Closure] Label Kont
;;      | If Closure Closure Kont
;;      | Mon Lab Lab Lab ContractClosure Kont
;;      | ChkCdr Lab Lab Lab ContractClosure Closure Kont
;;      | ChkOr Closure ContractClosure Lab Lab Lab ContractClosure Kont
;;      | MonAp [Listof ValClosure] [Listof ValClosure] [Listof ContractCLosure]
;;              Label Label Label Kont
(struct kont () #:transparent)
(struct mt kont () #:transparent)
(struct ap-k kont (vals args l k) #:transparent)
(struct if-k kont (then else k) #:transparent)
(struct mon-k kont (h f g con-clo k) #:transparent)
; ad-hoc frames for checking cdr of a pair, and right disjunction
(struct cdr-k kont (h f g con-clo clo k) #:transparent)
(struct or-k kont (clo con1 h f g con2 k) #:transparent)
; ad-hoc frames for monitoring arguments
(struct mon-ap-k (vs xs cs h f g k) #:transparent)

;; load : Program -> CEK
(define load
  (match-lambda
    [(prog mods main) (cek mods (close main ρ0) (mt))]))

;; kont-len : Kont -> Nat
(define kont-len
  (match-lambda
    [(mt) 0]
    [(ap-k v xs l k) (+ 1 (kont-len k))]
    [(if-k t e k) (+ 1 (kont-len k))]
    [(mon-k h f g c k) (+ 1 (kont-len k))]
    [(cdr-k h f g c cl k) (+ 1 (kont-len k))]
    [(or-k cl c h f g c2 k) (+ 1 (kont-len k))]
    [(mon-ap-k v x c h f g k) (+ 1 (kont-len k))]))

;; step : CEK -> CEK | [Setof CEK]
(define (step conf)
  (match-define (cek ms clo κ) conf)
  
  #;(begin ; check stack size
      (display (kont-len κ))
      (display "\n"))
  
  ;; refine-val : Value ContractClosure -> (Setof Value)
  (define (refine-val v c)
    (match-let ([(val u cs) v])
      (match u
        ['• ; TODO refactor
         (s-map
          (λ (cs1)
            (if (= 1 (set-count cs1))
                (match (first (set->list cs1))
                  [(or (contract-cl (flat-c (val (lam 1 (app (val 'equal? ∅) (list (ref 0) v) _) #f) cs)) ρc)
                       (contract-cl (flat-c (val (lam 1 (app (val 'equal? ∅) (list v (ref 0)) _) #f) cs)) ρc))
                   v] ; FIXME: v needs to be closed by ρc
                  [x (val u cs1)])
                (val u cs1)))
          (refine cs c))]
        [_ {set v}])))
  
  ;; refine-cl : ValClosure ContractClosure -> (Setof ValClosure)
  (define (refine-cl cl c)
    (match cl
      [(exp-cl v ρ) (s-map (λ (v1) (exp-cl v1 ρ)) (refine-val v c))]
      [_ {set cl} #|TODO|#]))
  
  ;; AMB : [Listof S-Exp] -> S-Exp
  (define (AMB exps)
    (match exps
      [`(,e) e]
      [`(,e ,e1 ...) `(if • ,e ,(AMB e1))]))
  
  ;; havoc : Label -> Exp
  (define (havoc from)
    (read-exp-with (hash) '() '() from
                   `(μ (y)
                       (λ (x)
                         ,(AMB `((y (x •)) (y (car x)) (y (cdr x))))))))
  
  ;; maybe-mon-k : Label Label Label ContractClosure Kont -> Kont
  (define (maybe-mon-k h f g c κ)
    ;; compact : Kont -> Kont
    (define (compact κ)
      (match κ
        [(mon-k h f g c1 κ1) (if (equal? c c1) κ1 (mon-k h f g c1 (compact κ1)))]
        [_ κ]))
    
    (mon-k h f g c (compact κ)))
  
  ;; bind-var-args : Natural [Listof ValClosure] -> [Listof ValClosure] ValClosure
  (define (bind-var-args n xs)
    (let-values ([(xs1 xs2) (split-at xs n)])
      (values xs1
              (foldr cons-cl (close (val 'nil ∅) ρ0) xs2))))
  
  ;; symbolic? : Closure -> Boolean
  (define symbolic?
    (match-lambda
      [(exp-cl e ρ) (symbolic-exp? e ρ)]
      [(cons-cl c1 c2) (or (symbolic? c1) (symbolic? c2))]
      [(mon-fn-cl h f g con c′) (symbolic? c′)]))
  
  ;; symbolic-exp? : Exp Env -> Boolean
  (define (symbolic-exp? e ρ)
    (match e
      [(ref x) (symbolic? (env-get x ρ))]
      [(val u cs) (equal? u '•)] ; TODO: handle false? nil? zero? cases better
      [(blame/ _1 _2) #f]
      [(app f xs _) (or (symbolic-exp? f ρ) (ormap (λ (x) (symbolic-exp? x ρ)) xs))]
      [(rec e) (symbolic-exp? e ρ)]
      [(if/ e1 e2 e3) (or (symbolic-exp? e1 ρ)
                          (symbolic-exp? e2 ρ)
                          (symbolic-exp? e3 ρ))]
      [(mon h f g c e) (symbolic-exp? e ρ)]
      [(mod-ref _f _l _m) #f]))
  
  ;; subst-mod-ref : Exp Label Label -> Exp
  (define (subst-mod-ref e1 m f e2)
    (define (subst e)
      (subst-mod-ref e m f e2))
    (match e1
      [(val (lam n body var?) cs) (val (lam n (subst body) var?) cs)]
      [(app f xs l) (app (subst f) (map subst xs) l)]
      [(rec b) (rec (subst b))]
      [(if/ e1 e2 e3) (if/ (subst e1) (subst e2) (subst e3))]
      [(mon h f g c e) (mon h f g c (subst e))]
      [(mod-ref m′ f′ l) (if (and (equal? m m′) (equal? f f′)) e2 e1)]
      [_ e1]))
  
  ;; abstr-func : Label Label Label FuncContract -> FuncExp
  (define (abstr-func h f g c)
    (match c ; PARTIAL
      [(func-c cs1 c2 var?)
       (mon h f g (func-c cs1 c2 var?)
            (val (lam (length cs1) (val '• {set (close-contract c2 ρ0)}) var?) ∅))]))
  
  ;; mk-func-• : Natural Boolean -> FuncExp
  (define (mk-func-• n var?)
    (val (lam n (val '• ∅) var?) ∅))
  
  
  ;; on-nonval : -> [Setof CEK]
  ;; determines machine's next state, dispatching on expression
  (define (on-nonval)
    (match-let ([(exp-cl e ρ) clo])
      (match e
        [(ref x) (cek ms (env-get x ρ) κ)]
        [(blame/ f h) (cek ms clo (mt))]
        [(app f xs l)
         (cek ms (close f ρ) (ap-k '() (map (λ (x) (close x ρ)) xs) l κ))]
        [(rec b) (cek ms (close b (env-extend clo ρ)) κ)]
        [(if/ e1 e2 e3)
         (let ([cl-test (close e1 ρ)]
               [cl-then (close e2 ρ)]
               [cl-else (close e3 ρ)])
           (match e1
             [(app (val u cs) `(,ar) _)
              (match ar
                ;; if it's a local variable, remember passed test in 'then' closure
                [(ref x) (let* ([cl (env-get x ρ)]
                                [cl1s (refine-cl cl (close-contract (flat-c (val u cs)) ρ))])
                           (if (set-empty? cl1s) ; test is gonna fail
                               (cek ms cl-else κ)
                               (s-map (λ (cl1) (cek ms cl-test
                                                    (if-k (close e2 (env-set x cl1 ρ))
                                                          cl-else κ)))
                                      cl1s)))]
                [_ (cek ms cl-test (if-k cl-then cl-else κ))])]
             [_ (cek ms cl-test (if-k cl-then cl-else κ))]))]
        [(mon h f g c e1)
         (cek ms (close e1 ρ) (mon-k h f g (close-contract c ρ) κ))]
        [(mod-ref m f l)
         (let* ([mod (mod-by-name ms m)]
                [defn (modl-get-defn mod f)]
                [v
                 (match defn
                   [(val (lam n body var?) cs)
                    (match κ
                      [(ap-k '() xs _ κ1)
                       (if (ormap symbolic? xs)
                           (subst-mod-ref defn m f
                                          (if (modl-provides? mod f)
                                              (abstr-func m m l (modl-get-contract mod f))
                                              (mk-func-• n var?)))
                           defn)]
                      [_ defn])]
                   [_ defn])])
           (if (equal? m l)
               (if (modl-provides? mod f)
                   (match v
                     [(val '• cs)
                      (s-map
                       (λ (v) (cek ms (close v ρ0) κ))
                       (refine-val v (close-contract (modl-get-contract mod f) ρ0)))]
                     [_ (cek ms (close v ρ0) κ)])
                   (cek ms (close v ρ0) κ))
               (let ([c (modl-get-contract mod f)])
                 (match v
                   [(val '• cs)
                    (let* ([C (close-contract c ρ0)]
                           [κ1 (mon-k m m l C κ)])
                      (s-map (λ (v) (cek (upd-mod-by-name ms m f (const v))
                                         (close v ρ0)
                                         κ1))
                             (refine-val v C)))]
                   [_ (cek ms (close v ρ0)
                           (mon-k m m l (close-contract c ρ) κ))]))))])))
  
  ;; on-val : -> [Setof CEK]
  ;; determines machine's next state, dispatching on kont
  (define (on-val)
    (match κ
      [(mt) conf]
      [(ap-k vs (cons x xs) l κ) ; eval next arg
       (cek ms x (ap-k (cons clo vs) xs l κ))]
      [(ap-k vals '() l κ) ; apply function/prim-op
       (match-let ([(cons f xs) (reverse (cons clo vals))])
         (match f
           [(exp-cl (val u cs) ρv)
            (match u
              [(lam n e var-args?)
               (if (or (and var-args? (<= (- n 1) (length xs)))
                       (= n (length xs))) ; arity check
                   ; delay approximating arguments until this point
                   ; to avoid false blames in earlier stages
                   ; FIXME: disable approximating for now
                   #;(let ([zs (if (andmap concrete? xs) xs (map approx xs))])
                       (cek ms (close e (env-extendl zs ρv)) κ))
                   (if var-args?
                       (let-values ([(zs z) (bind-var-args (- n 1) xs)])
                         (cek ms (close e (env-extend z (env-extendl zs ρv))) κ))
                       (cek ms (close e (env-extendl xs ρv)) κ))
                   (cek ms (close (blame/ l '∆) ρ0) (mt)))]
              ['•
               {non-det
                (match-lambda
                  [#t {set-union
                       (list->set
                        (map (λ (x)
                               (cek ms (close (havoc l) ρ0)
                                    (ap-k '() `(,x) l (mt))))
                             xs))
                       ; value(s) refined by function's contract's range
                       (s-map
                        (λ (v) (cek ms (close v ρ0) κ))
                        (for/fold ([vs {set (val '• ∅)}]) ([c cs])
                          (match c
                            [(contract-cl (func-c cs1 c2 _) ρc)
                             (let ([c2-cl (close-contract c2 (env-extend xs ρc))])
                               (non-det (λ (v) (refine-val v c2-cl)) vs))]
                            [_ vs])))}]
                  [#f {set (cek ms (close (blame/ l '∆) ρ0) (mt))}])
                (proc-with-arity? f (length xs))}]
              [_ (if (prim? u) ; primitive op handles arity check on its own
                     (s-map (λ (cl) (cek ms cl κ)) (δ u xs l))
                     (cek ms (close (blame/ l '∆) ρ0) (mt)))])]
           [(mon-fn-cl h f g (contract-cl (func-c cs1 c2 var-args?) ρc) clo1)
            (if (or (and var-args? (<= (- (length cs1) 1) (length xs)))
                    (= (length cs1) (length xs)))
                (s-map
                 (match-lambda
                   [#t (cek ms clo1
                            (mon-ap-k
                             '() xs (map (λ (c) (close-contract c ρc)) cs1) h g f
                             (maybe-mon-k ; monitor result
                              h f g (close-contract c2 (env-extendl xs ρc)) κ)))]
                   [#f (cek ms (close (blame/ f h) ρ0) (mt))])
                 (proc-with-arity? clo1 (length xs)))
                (cek ms (close (blame/ l h) ρ0) (mt)))]
           [_ (cek ms (close (blame/ l '∆) ρ0) (mt))]))]
      [(if-k clo1 clo2 κ)
       (non-det (match-lambda
                  [(exp-cl (val #t cs) ρv) {set (cek ms clo1 κ)}]
                  [(exp-cl (val #f cs) ρv) {set (cek ms clo2 κ)}])
                (δ 'true? (list clo) '†))]
      [(mon-k h f g con-cl κ)
       (match-let ([(contract-cl c ρc) con-cl])
         (match (maybe-FC `(,0) c)
           [`(,(ref x))
            (let ([pred-or-contract (env-get x ρc)])
              (if (contract-cl? pred-or-contract)
                  (cek ms clo (mon-k h f g pred-or-contract κ))
                  (match (verify clo con-cl) ; TODO: code duplication, temp
                    ['Proved (cek ms clo κ)]
                    ['Refuted (cek ms (close (blame/ f h) ρ0) (mt))]
                    ['Neither
                     (s-map (λ (v)
                              (cek ms pred-or-contract
                                   (ap-k '() `(,clo) h #|TODO: is h the right label?|#
                                         (if-k v (close (blame/ f h) ρ0) κ))))
                            (refine-cl clo con-cl))])))]
           [`(,pred)
            (match (verify clo con-cl)
              ['Proved (cek ms clo κ)]
              ['Refuted (cek ms (close (blame/ f h) ρ0) (mt))]
              ['Neither
               (s-map (λ (v)
                        (cek ms (close pred ρc)
                             (ap-k '() `(,clo) h #|TODO: is h the right label?|#
                                   (if-k v (close (blame/ f h) ρ0) κ))))
                      (refine-cl clo con-cl))])]
           [`()
            (match c
              [(func-c cs1 c2 _) ; delay var-args checking
               (s-map (match-lambda
                        [#t (cek ms (mon-fn-cl h f g con-cl clo) κ)]
                        [#f (cek ms (close (blame/ f h) ρ0) (mt))])
                      (proc-with-arity? clo (length cs1)))]
              [(cons-c c1 c2)
               (s-map
                (match-lambda
                  [`(,cl1 ,cl2)
                   (cek ms cl1 (mon-k h f g (close-contract c1 ρc)
                                      (cdr-k h f g (close-contract c2 ρc) cl2 κ)))]
                  ['() (cek ms (exp-cl (blame/ f h) ρ0) (mt))])
                (split-cons clo))]
              [(or-c c1 c2)
               (match (verify clo (close-contract c1 ρc))
                 ['Proved (cek ms clo κ)]
                 ['Refuted (cek ms clo (mon-k h f g (close-contract c2 ρc) κ))]
                 ['Neither
                  (match (maybe-FC `(,0) c1)
                    [`(,pred)
                     (cek ms (close pred ρc)
                          (ap-k '() `(,clo) h #|TODO: is h the right label?|#
                                (or-k clo (close-contract c1 ρc)
                                      h f g (close-contract c2 ρc) κ)))]
                    [`() (error "left disjunction is not flat: " c1)])])]
              [(and-c c1 c2)
               (cek ms clo
                    (mon-k h f g (close-contract c1 ρc)
                           (mon-k h f g (close-contract c2 ρc) κ)))]
              [(rec-c c1)
               (cek ms clo 
                    (mon-k h f g
                           (close-contract c1 (env-extend con-cl ρc)) κ))]
              [(ref-c x)
               (cek ms clo (mon-k h f g (env-get x ρc) κ))])]))]
      [(cdr-k h f g c clo1 κ)
       (cek ms clo1
            (mon-k h f g c
                   (ap-k `(,clo ,(close (val 'cons ∅) ρ0)) '()
                         h #|TODO: h, right label?|# κ)))]
      [(or-k clo1 c1 h f g c2 κ)
       (non-det (λ (r)
                  (match (val-pre (exp-cl-exp r))
                    [#t (s-map (λ (clo) (cek ms clo κ))
                               (refine-cl clo1 c1))]
                    [#f {set (cek ms clo1 (mon-k h f g c2 κ))}]))
                (δ 'true? `(,clo) h))]
      [(mon-ap-k vs (cons x xs) (cons c cs) h g f κ)
       (cek ms x (mon-k
                  h g f c
                  (mon-ap-k (cons clo vs)
                            xs
                            (if (empty? cs) (cons c cs) cs #|support var-args|#)
                            h g f κ)))]
      [(mon-ap-k vs '() _ h g f κ)
       (cek ms clo (ap-k vs '() f κ))]))
  
  (if (val-cl? clo) (on-val) (on-nonval)))

;; EvalAnswer := Number | Boolean | '• | '(blame Label Label)
;;            | 'function | (cons EvalAnswser EvalAnswer)
;; eval-answer? : Any -> Boolean
(define (eval-answer? x)
  (match x
    [`(blame ,l1 ,l2) (and (symbol? l1) (symbol? l2))]
    [`(cons ,x ,xs) (and (eval-answer? x) (eval-answer? xs))]
    [else (or (number? x) (boolean? x) (eq? 'nil x) (string? x)
              (member x `(function •)))]))

;; eval-cek : S-Exp -> [Setof EvalAnswer]
;; evaluates closed, well-typed SCPCF term
(define (eval-cek p)
  
  ;; final? : CEK -> Boolean
  (define (final? conf)
    (match-let ([(cek _ clo κ) conf])
      (and (mt? κ)
           (or (cons-cl? clo)
               (mon-fn-cl? clo)
               (answer? (exp-cl-exp clo))))))
  
  ;; run : CEK -> [Setof CEK]
  (define (run conf)
    
      ;; INVARIANT:
      ;; -- known: states whose next states are explored
      ;; -- unknown: non-final states whose next states are unexplored
      ;; -- final: final states (~ answers)
      (let loop ([known ∅] [unknown {set conf}] [final ∅])
        (cond
          [(set-empty? unknown) final]
          [else
           (define known1 (set-union known unknown))
           (define (on-new-state unknowns finals s)
             (cond
               [(final? s) (values unknowns (set-add finals s))]
               [(set-member? known1 s) (values unknowns finals)]
               [else (values (set-add unknowns s) finals)]))
           (define-values (unknown1 final1)
             (for/fold ([unknown1 ∅] [final1 final]) ([u (in-set unknown)])
               (let ([next (step u)])
                 (cond
                   [(set? next)
                    (for/fold ([unknown2 unknown1] [final2 final1]) ([n (in-set next)])
                      (on-new-state unknown2 final2 n))]
                   [else (on-new-state unknown1 final1 next)]))))
           
           (loop known1 unknown1 final1)])))
  
  ;; get-answer : Closure -> [Setof EvalAnswer]
  (define (get-answer clo)
    (match clo
      [(exp-cl e ρ)
       (match e
         [(val u cs) (match u
                       [(lam n b _) {set 'function}]
                       ['•
                        (cond
                          [(set-member? cs (mk-contract-cl 'nil?)) {set 'nil}]
                          [(set-member? cs (mk-contract-cl 'false?)) {set #f}]
                          [(set-member? cs (mk-contract-cl 'zero?)) {set 0}]
                          [(equal? (contracts-imply? cs 'proc?) 'Proved) {set 'function}]
                          [else {set '•}])]
                       [u {set (if (prim? u) 'function u)}])]
         [(blame/ l1 l2) {set `(blame ,l1 ,l2)}])]
      [(mon-fn-cl h f g conclo clo) {set 'function}]
      [(cons-cl cl1 cl2)
       (let ([s1 (get-answer cl1)]
             [s2 (get-answer cl2)])
         (non-det (λ (x1)
                    (non-det (λ (x2)
                               {set `(cons ,x1 ,x2)})
                             s2))
                  s1))]))
  
  (non-det (compose get-answer cek-clo) (run (load (read-prog p)))))

;; verify : Closure ContractClosure -> Verified
;; Verified := 'Proved | 'Refuted | 'Neither
(define (verify clo conclo)
  (match clo
    [(exp-cl (val u cs) ρ)
     (match conclo
       [(contract-cl (val p _) ρc)
        (cond
          [(prim? p) (contracts-imply? cs p)]
          [(set-member? cs conclo) 'Proved]
          [else 'Neither])]
       [_ (if (set-member? cs conclo) 'Proved 'Neither)])]
    [else 'Neither #|TODO|#]))

;; maybe-FC : [Listof Natural] Contract -> [List Exp] or Empty
;; converts flat contract to predicate;
;; OR returns reference to (predicate|contract) (i feel sooo dirty)
;; whether result expression is closed or open depends on original contract
;; -- ds: (list-ref ds k) is number of extra levels of λ introduced
;;        after the k-th (μ.C)
(define (maybe-FC ds c)
  
  ;; generates conjunction
  (define (and/ . exps)
    (match exps
      [`(,e1 ,e2 ,es ...) (if/ e1 (apply and/ (rest exps)) (val #f ∅))]
      [`(,e1) e1]
      [_ (val #t ∅)]))
  
  ;; generates disjunction
  (define (or/ . exps)
    (match exps
      [`(,e1 ,e2 ,es ...) (if/ e1 (val #t ∅) (apply or/ (rest exps)))]
      [`(,e1) e1]
      [_ (val #f ∅)]))
  
  ;; lift : [X_1 ... X_n -> Y] [Maybe X_1] ... [Maybe X_n] -> [Maybe Y]
  ;; , where [Maybe X] = [List X] | Empty
  ;; apply given function, allowing for failures in its arguments
  (define (lift f . xss)
    (cond
      [(andmap cons? xss) (cons (apply f (map car xss))
                                (apply (curry lift f) (map cdr xss)))]
      [else empty]))
  
  ;; car+1 : [Listof Natural] -> [Listof Natural]
  ;; adds 1 to list's first element if exists
  (define (car+1 xs)
    (match xs
      [(cons x zs) (cons (+ 1 x) zs)]
      [_ xs]))
  
  (match c
    [(flat-c p) (list (shift (apply + ds) p))]
    [(func-c cs d _) empty]
    [(cons-c c1 c2) (lift (λ (p1 p2)
                            (val (lam 1
                                      (and/ (app (val 'cons? ∅) `(,(ref 0)) '☠ #|TODO|#)
                                            (app p1 `(,(app (val 'car ∅) `(,(ref 0)) '☠ #|TODO|#)) '☠ #|TODO|#)
                                            (app p2 `(,(app (val 'cdr ∅) `(,(ref 0)) '☠ #|TODO|#)) '☠ #|TODO|#))
                                      #f)
                                 ∅))
                          (maybe-FC (car+1 ds) c1)
                          (maybe-FC (car+1 ds) c2))]
    [(or-c c1 c2) (lift (λ (p1 p2)
                          (val (lam 1
                                    (or/ (app p1 `(,(ref 0)) '☠ #|TODO|#)
                                         (app p2 `(,(ref 0)) '☠ #|TODO|#))
                                    #f)
                               ∅))
                        (maybe-FC (car+1 ds) c1)
                        (maybe-FC (car+1 ds) c2))]
    [(and-c c1 c2) (lift (λ (p1 p2)
                           (val (lam 1
                                     (and/ (app p1 `(,(ref 0)) '☠ #|TODO|#)
                                           (app p2 `(,(ref 0)) '☠ #|TODO|#))
                                     #f)
                                ∅))
                         (maybe-FC (car+1 ds) c1)
                         (maybe-FC (car+1 ds) c2))]
    [(rec-c c1) (lift rec (maybe-FC (cons 0 ds) c1))]
    [(ref-c x) (list (ref (+ (car ds) x)))]))

;; for debugging only
(define (pow f n) (apply compose (make-list n f)))
(define f (curry non-det step))
(define (s n) (pow f n))
