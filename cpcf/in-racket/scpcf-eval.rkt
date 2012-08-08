#lang racket

(require rackunit)
(require racket/contract)
(require "scpcf-lang.rkt")
(require "env.rkt")
(require "bi-map.rkt")

(provide
 (contract-out
  [load (prog? . -> . cek?)]
  [step (cek? . -> . (set/c cek?))]
  [eval-cek (s-exp? . -> . (set/c eval-answer?))]
  
  [eval-answer? (any/c . -> . boolean?)]))

(define hist0 empty-bi-map)

;; CEK = (cek History [Listof Module] Closure Kont)
(struct cek (hist ms clo kont) #:transparent)

;; Kont = Mt
;;      | Ap [Listof ValClosure] [Listof Closure] Label Kont
;;      Abuse kont frame to remember passed tests
;;      | If [(List Label ContractClosure)|'()] Closure Closure Kont
;;      | Mon Lab Lab Lab ContractClosure Kont
;;      | ChkCdr Lab Lab Lab ContractClosure Closure Kont
;;      | ChkOr Closure ContractClosure Lab Lab Lab ContractClosure Kont
;;      | MonAp [Listof ValClosure] [Listof ValClosure] [Listof ContractCLosure]
;;              Label Label Label Kont
(struct kont () #:transparent)
(struct mt kont () #:transparent)
(struct ap-k kont (vals args l k) #:transparent)
(struct if-k kont (passed then else k) #:transparent)
(struct mon-k kont (h f g con-clo k) #:transparent)
; ad-hoc frames for checking cdr of a pair, and right disjunction
(struct cdr-k kont (h f g con-clo clo k) #:transparent)
(struct or-k kont (clo con1 h f g con2 k) #:transparent)
; ad-hoc frames for monitoring arguments
(struct mon-ap-k (vs xs cs h f g k) #:transparent)

;; load : Program -> CEK
(define load
  (match-lambda
    [(prog mods main) (cek hist0 mods (close main ρ0) (mt))]))

;; kont-len : Kont -> Nat
(define kont-len
  (match-lambda
    [(mt) 0]
    [(ap-k v xs l k) (+ 1 (kont-len k))]
    [(if-k p t e k) (+ 1 (kont-len k))]
    [(mon-k h f g c k) (+ 1 (kont-len k))]
    [(cdr-k h f g c cl k) (+ 1 (kont-len k))]
    [(or-k cl c h f g c2 k) (+ 1 (kont-len k))]
    [(mon-ap-k v x c h f g k) (+ 1 (kont-len k))]))

;; step : CEK -> [Setof CEK]
(define (step conf)
  (match-define (cek hist ms clo κ) conf)
  
  #;(begin ; check stack size
      (display (kont-len κ))
      (display "\n"))
  
  ;; refine-val : Value ContractClosure -> (Setof Value)
  (define (refine-val v c)
    (match-let ([(val u cs) v])
      (match u
        ['• (s-map (λ (cs1) (val u cs1)) (refine cs c))]
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
    (read-exp-with '() from
                   `(μ (y)
                       (λ (x)
                         ,(AMB `((y (x •)) (y (car x)) (y (cdr x))))))))
  
  ;; maybe-ap-k : Closure [Listof ValClosure] [Listof Closure] Label -> [SetOf CEK]
  ;; decides whether to add another application kont frame or approximate it
  (define (maybe-ap-k f vs xs l)
    ; FIXME: turned out i forgot to remember the function
    (let ([next-frame-sig (ap-k vs xs l (mt))])
      (if (bi-map-has-val? hist next-frame-sig) ; dejavu
          (short-cut clo)
          {set (cek (bi-map-set hist κ next-frame-sig)
                    ms
                    f
                    (ap-k vs xs l κ))})))
  
  ;; maybe-mon-k : Label Label Label ContractClosure Kont -> Kont
  (define (maybe-mon-k h f g c κ)
    ;; already? : Kont -> Bool
    (define (already? κ)
      (match κ
        [(mon-k h f g c1 κ1) (if (equal? c c1) #t (already? κ1))]
        [_ #f]))
    
    (if (already? κ) κ
        (mon-k h f g c κ)))
  
  ;; short-cut : Closure -> {Setof CEK}
  (define (short-cut cl)
    (match cl
      [(exp-cl v ρ)
       (match v
         [(val u cs) {set (cek hist ms cl κ)}]
         [(app f xs l) {set (cek hist ms (close (val '• ∅) ρ0) κ)}]
         [(mon h f g c e) (set-add
                           (s-map (λ (cs) (cek hist ms (close (val '• cs) ρ0) κ))
                                  (refine ∅ (close-contract c ρ)))
                           (cek hist0 ms (close (blame/ f h) ρ0) κ))])]
      [_ {set (cek hist ms cl κ)}]))
  
  ;; on-nonval : -> [Setof CEK]
  ;; determines machine's next state, dispatching on expression
  (define (on-nonval)
    (match-let ([(exp-cl e ρ) clo])
      (match e
        [(ref x) {set (cek hist ms (env-get x ρ) κ)}]
        [(blame/ f h) {set (cek hist0 ms clo (mt))}]
        [(app f xs l)
         (maybe-ap-k (close f ρ) '() (map (λ (e) (close e ρ)) xs) l)]
        [(rec b) {set (cek hist ms (close b (env-extend clo ρ)) κ)}]
        [(if/ e1 e2 e3)
         (let ([cl-test (close e1 ρ)]
               [cl-then (close e2 ρ)]
               [cl-else (close e3 ρ)])
           (match e1
             [(app (val u cs) `(,ar) _)
              (match ar
                ;; if it's a local variable, remember passed test in 'then' closure
                [(ref x) (let ([cl (env-get x ρ)])
                           (s-map (λ (cl1)
                                    (cek hist ms cl-test
                                         (if-k '()
                                               (close e2 (env-set x cl1 ρ))
                                               cl-else κ)))
                                  (refine-cl cl (close-contract (flat-c (val u cs)) ρ))))]
                ;; if it's a module reference, abuse kont frame to modify module later
                [(mod-ref a _)
                 {set (cek hist ms cl-test (if-k `(,a ,(close-contract (flat-c (val u cs)) ρ))
                                                 cl-then cl-else κ))}]
                [_ {set (cek hist ms cl-test (if-k '() cl-then cl-else κ))}])]
             [_ {set (cek hist ms cl-test (if-k '() cl-then cl-else κ))}]))]
        [(mon h f g c e1)
         {set (cek hist ms (close e1 ρ) (mon-k h f g (close-contract c ρ) κ))}]
        [(mod-ref f g) (match-let ([(modl f c v) (mod-by-name f ms)])
                         (if (equal? f g)
                             {set (cek hist ms (close v ρ0) κ)}
                             (match v
                               ; TODO: page 8: isn't (mon f f g C (• · C)) the same as (• · C) ?
                               [(val '• cs)
                                (let* ([C (close-contract c ρ)]
                                       [κ1 (mon-k f f g C κ)])
                                  (s-map (λ (v) (cek hist
                                                     (upd-mod-by-name f (const v) ms)
                                                     (close v ρ)
                                                     κ1))
                                         (refine-val v C)))]
                               [_ {set (cek hist ms (close v ρ)
                                            (mon-k f f g (close-contract c ρ) κ))}])))])))
  
  ;; on-val : -> [Setof CEK]
  ;; determines machine's next state, dispatching on kont
  (define (on-val)
    (match κ
      [(mt) {set conf}]
      [(ap-k vs (cons x xs) l κ) ; eval next arg
       {set (cek hist ms x (ap-k (cons clo vs) xs l κ))}]
      [(ap-k vals '() l κ) ; apply function/prim-op
       (match-let ([(cons f xs) (reverse (cons clo vals))]
                   [hist1 (bi-map-del-key hist κ)])
         (match f
           [(exp-cl (val u cs) ρv)
            (match u
              [(lam n e) {set (if (= n (length xs)) ; arity check
                                  ; delay approximating arguments until this point
                                  ; to avoid false blames in earlier stages
                                  #;(let ([zs (if (andmap concrete? xs) xs (map approx xs))])
                                      (cek hist1 ms (close e (env-extendl zs ρv)) κ))
                                  (cek hist1 ms (close e (env-extendl xs ρv)) κ)
                                  (cek hist0 ms (close (blame/ l '∆) ρ0) (mt)))}]
              ['•
               {non-det
                (match-lambda
                  [#t {set-add
                       (list->set
                        (map (λ (x)
                               (cek hist0 ms (close (havoc l) ρ0)
                                    (ap-k '() `(,x) l (mt))))
                             xs))
                       (cek ; value refined by function's contract's range
                        hist1
                        ms
                        (close
                         (val '•
                              (for/fold ([acc ∅]) ([c cs])
                                (match c
                                  [(contract-cl (func-c cs1 c2) ρc)
                                   (set-add acc (close-contract c2 (env-extend xs ρc)))]
                                  [_ acc])))
                         ρ0)
                        κ)}]
                  [#f {set (cek hist0 ms (close (blame/ l '∆) ρ0) (mt))}])
                (proc-with-arity? f (length xs))}]
              [_ (if (prim? u) ; primitive op handles arity check on its own
                     (s-map (λ (cl) (cek hist1 ms cl κ)) (δ u xs l))
                     {set (cek hist0 ms (close (blame/ l '∆) ρ0) (mt))})])]
           [(mon-fn-cl h f g (contract-cl (func-c cs1 c2) ρc) clo1)
            (if (= (length xs) (length cs1))
                (s-map
                 (match-lambda
                   [#t (cek hist1 ms clo1
                            (mon-ap-k
                             '() xs (map (λ (c) (close-contract c ρc)) cs1) h g f
                             (maybe-mon-k ; monitor result
                              h f g (close-contract c2 (env-extendl xs ρc)) κ)))]
                   [#f (cek hist0 ms (close (blame/ f h) ρ0) (mt))])
                 (proc-with-arity? clo1 (length cs1)))
                {set (cek hist0 ms (close (blame/ l h) ρ0) (mt))})]
           [_ {set (cek hist0 ms (close (blame/ l '∆) ρ0) (mt))}]))]
      [(if-k passed clo1 clo2 κ)
       (non-det (match-lambda
                  [(exp-cl (val #t cs) ρv)
                   (match passed
                     [`(,l ,ccl) (match-let* ([(modl l c v) (mod-by-name l ms)])
                                   (s-map (λ (v1)
                                            (cek hist (upd-mod-by-name l (const v1) ms)
                                                 clo1 κ))
                                          (refine-val v ccl)))]
                     ['() {set (cek hist ms clo1 κ)}])]
                  [(exp-cl (val #f cs) ρv)
                   {set (cek hist ms clo2 κ)}])
                (δ 'true? (list clo) '†))]
      [(mon-k h f g con-cl κ)
       (match-let ([(contract-cl c ρc) con-cl])
         (match (maybe-FC `(,0) c)
           [`(,(ref x))
            (let ([pred-or-contract (env-get x ρc)])
              (if (contract-cl? pred-or-contract)
                  {set (cek hist ms clo (mon-k h f g pred-or-contract κ))}
                  (match (verify clo con-cl) ; TODO: code duplication, temp
                    ['Proved {set (cek hist ms clo κ)}]
                    ['Refuted {set (cek hist0 ms (close (blame/ f h) ρ0) (mt))}]
                    ['Neither
                     (s-map (λ (v)
                              (cek hist ms pred-or-contract
                                   (ap-k '() `(,clo) h #|TODO: is h the right label?|#
                                         (if-k '() v (close (blame/ f h) ρ0) κ))))
                            (refine-cl clo con-cl))])))]
           [`(,pred)
            (match (verify clo con-cl)
              ['Proved {set (cek hist ms clo κ)}]
              ['Refuted {set (cek hist0 ms (close (blame/ f h) ρ0) (mt))}]
              ['Neither
               (s-map (λ (v)
                        (cek hist ms (close pred ρc)
                             (ap-k '() `(,clo) h #|TODO: is h the right label?|#
                                   (if-k '() v (close (blame/ f h) ρ0) κ))))
                      (refine-cl clo con-cl))])]
           [`()
            (match c
              [(func-c cs1 c2)
               (s-map (match-lambda
                        [#t (cek hist ms (mon-fn-cl h f g con-cl clo) κ)]
                        [#f (cek hist0 ms (close (blame/ f h) ρ0) (mt))])
                      (proc-with-arity? clo (length cs1)))]
              [(cons-c c1 c2)
               (s-map
                (match-lambda
                  [`(,cl1 ,cl2)
                   (cek hist ms cl1 (mon-k h f g (close-contract c1 ρc)
                                           (cdr-k h f g (close-contract c2 ρc) cl2 κ)))]
                  ['() (cek hist0 ms (exp-cl (blame/ f h) ρ0) (mt))])
                (split-cons clo))]
              [(or-c c1 c2)
               {set
                (match (verify clo (close-contract c1 ρc))
                  ['Proved (cek hist ms clo κ)]
                  ['Refuted (cek hist ms clo (mon-k h f g (close-contract c2 ρc) κ))]
                  ['Neither
                   (match (maybe-FC `(,0) c1)
                     [`(,pred)
                      (cek hist ms (close pred ρc)
                           (ap-k '() `(,clo) h #|TODO: is h the right label?|#
                                 (or-k clo (close-contract c1 ρc)
                                       h f g (close-contract c2 ρc) κ)))]
                     [`() (error "left disjunction is not flat: " c1)])])}]
              [(and-c c1 c2)
               {set (cek hist ms clo
                         (mon-k h f g (close-contract c1 ρc)
                                (mon-k h f g (close-contract c2 ρc) κ)))}]
              [(rec-c c1)
               {set (cek hist ms clo 
                         (mon-k h f g
                                (close-contract c1 (env-extend con-cl ρc)) κ))}]
              [(ref-c x)
               {set (cek hist ms clo (mon-k h f g (env-get x ρc) κ))}])]))]
      [(cdr-k h f g c clo1 κ)
       {set (cek hist ms clo1
                 (mon-k h f g c
                        (ap-k `(,clo ,(close (val 'cons ∅) ρ0)) '()
                              h #|TODO: h, right label?|# κ)))}]
      [(or-k clo1 c1 h f g c2 κ)
       (non-det (λ (r)
                  (match (val-pre (exp-cl-exp r))
                    [#t (s-map (λ (clo) (cek hist ms clo κ))
                               (refine-cl clo1 c1))]
                    [#f {set (cek hist ms clo1 (mon-k h f g c2 κ))}]))
                (δ 'true? `(,clo) h))]
      [(mon-ap-k vs (cons x xs) (cons c cs) h g f κ)
       {set
        (cek hist ms x (mon-k
                        h g f c
                        (mon-ap-k (cons clo vs) xs cs h g f κ)))}]
      [(mon-ap-k vs '() '() h g f κ)
       {set (cek hist ms clo (ap-k vs '() f κ))}]))
  
  (if (val-cl? clo) (on-val) (on-nonval)))

;; EvalAnswer := Number | Boolean | '• | '(blame Label Label)
;;            | 'function | (cons EvalAnswser EvalAnswer)
;; eval-answer? : Any -> Boolean
(define (eval-answer? x)
  (match x
    [`(blame ,l1 ,l2) (and (symbol? l1) (symbol? l2))]
    [`(cons ,x ,xs) (and (eval-answer? x) (eval-answer? xs))]
    [else (or (number? x) (boolean? x) (eq? 'nil x)
              (member x `(function •)))]))

;; eval-cek : S-Exp -> [Setof EvalAnswer]
;; evaluates closed, well-typed SCPCF term
(define (eval-cek p)
  
  ;; final? : CEK -> Boolean
  (define (final? conf)
    (match-let ([(cek hist _ clo κ) conf])
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
         (define-values (final1 unknown1)
           (for/fold ([final1 final] [unknown1 ∅]) ([next (non-det step unknown)])
             (cond
               [(final? next) (values (set-add final1 next) unknown1)]
               [(set-member? known1 next) (values final1 unknown1)]
               [else (values final1 (set-add unknown1 next))])))
         
         (loop known1 unknown1 final1)])))
  
  ;; get-answer : Closure -> [Setof EvalAnswer]
  (define (get-answer clo)
    (match clo
      [(exp-cl e ρ)
       (match e
         [(val u cs) (match u
                       [(lam n b) {set 'function}]
                       ['•
                        (cond
                          [(set-member? cs (mk-contract-cl 'nil?)) {set 'nil}]
                          [(set-member? cs (mk-contract-cl 'false?)) {set #f}]
                          [(set-member? cs (mk-contract-cl 'bool?)) {set #t #f}]
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
    [(func-c cs d) empty]
    [(cons-c c1 c2) (lift (λ (p1 p2)
                            (val (lam 1 (and/ (app (val 'cons? ∅) `(,(ref 0)) '☠ #|TODO|#)
                                              (app p1 `(,(app (val 'car ∅) `(,(ref 0)) '☠ #|TODO|#)) '☠ #|TODO|#)
                                              (app p2 `(,(app (val 'cdr ∅) `(,(ref 0)) '☠ #|TODO|#)) '☠ #|TODO|#)))
                                 ∅))
                          (maybe-FC (car+1 ds) c1)
                          (maybe-FC (car+1 ds) c2))]
    [(or-c c1 c2) (lift (λ (p1 p2)
                          (val (lam 1 (or/ (app p1 `(,(ref 0)) '☠ #|TODO|#)
                                           (app p2 `(,(ref 0)) '☠ #|TODO|#)))
                               ∅))
                        (maybe-FC (car+1 ds) c1)
                        (maybe-FC (car+1 ds) c2))]
    [(and-c c1 c2) (lift (λ (p1 p2)
                           (val (lam 1 (and/ (app p1 `(,(ref 0)) '☠ #|TODO|#)
                                             (app p2 `(,(ref 0)) '☠ #|TODO|#)))
                                ∅))
                         (maybe-FC (car+1 ds) c1)
                         (maybe-FC (car+1 ds) c2))]
    [(rec-c c1) (lift rec (maybe-FC (cons 0 ds) c1))]
    [(ref-c x) (list (ref (+ (car ds) x)))]))

;; for debugging only
(define (pow f n) (apply compose (make-list n f)))
(define f (curry non-det step))
(define (s n) (pow f n))
