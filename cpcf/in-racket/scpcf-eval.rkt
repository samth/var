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

;; step : CEK -> [Setof CEK]
(define (step conf)
  (match-define (cek ms clo κ) conf)
  
  ;; refine : Closure ContractClosure -> Val
  (define (refine clo conclo)
    (match clo
      [(exp-cl (val u cs) ρ) (exp-cl (val u (set-add cs conclo)) ρ)]
      [else clo #|TODO|#]))
  
  ;; TODO: does this alter semantics compared to old 'havoc' and AMB,
  ;;       with nondeterminism 'embedded' in the object language?
  ;; havocs :: [Listof Exp]
  (define havocs
    (map (λ (sub) (read-exp `(μ (y)
                                (λ (x) ; relies in this 'x' being that 'x'
                                  (y ,sub)))))
         `((x •) (car x) (cdr x))))
  
  ;; on-nonval : -> [Setof CEK]
  ;; determines machine's next state, dispatching on expression
  (define (on-nonval)
    (match-let ([(exp-cl e ρ) clo])
      {set
       (match e
         [(ref x) (cek ms (env-get x ρ) κ)]
         [(blame/ f h) (cek ms clo (mt))]
         [(app f xs l)
          (cek ms (close f ρ) (ap-k '() (map (λ (e) (close e ρ)) xs) l κ))]
         [(rec b) (cek ms (close b (env-extend clo ρ)) κ)]
         [(if/ e1 e2 e3)
          (cek ms (close e1 ρ) (if-k (close e2 ρ) (close e3 ρ) κ))]
         [(mon h f g c e1)
          (cek ms (close e1 ρ) (mon-k h f g (close-contract c ρ) κ))]
         [(mod-ref f g) (match-let ([(modl f c v) (mod-by-name f ms)])
                          (if (equal? f g)
                              (cek ms (close v ρ0) κ)
                              (match v
                                ; TODO: page 8: isn't (mon f f g C (• · C)) the same as (• · C) ?
                                [(val '• cs) (cek ms (close (mon f f g c (val '• (set-add cs (close-contract c ρ0)))) ρ0) κ)]
                                [_ (cek ms (close (mon f f g c v) ρ0) κ)])))])}))
  
  ;; on-val : -> [Setof CEK]
  ;; determines machine's next state, dispatching on kont
  (define (on-val)
    (match κ
      [(mt) {set conf}]
      [(ap-k vs (cons x xs) l κ) ; eval next arg
       {set (cek ms x (ap-k (cons clo vs) xs l κ))}]
      [(ap-k vals '() l κ) ; apply function/prim-op
       (match-let ([(cons f xs) (reverse (cons clo vals))])
         (match f
           [(exp-cl (val u cs) ρv)
            (match u
              [(lam n e) {set (if (= n (length xs)) ; arity check
                                  (cek ms (close e (env-extendl xs ρv)) κ)
                                  (cek ms (close (blame/ l '∆) ρ0) (mt)))}]
              ['•
               {non-det
                (match-lambda
                  [#t (set-add
                       (list->set
                        (map (λ (havoc) ; TODO wrong
                               (cek ms (close havoc ρ0)
                                    (ap-k '() xs l #|TODO right label?|#
                                          (mt) #|TODO is it safe to kill κ?|#)))
                             havocs))
                       (cek ; value refined by function's contract's range
                        ms
                        (close
                         (val '•
                              (s-map
                               (λ (c)
                                 (match c
                                   [(contract-cl (func-c cs1 c2) ρc)
                                    (close-contract c2 (env-extend xs ρc))]))
                               cs))
                         ρ0)
                        κ))]
                  [#f {set (cek ms (close (blame/ l '∆) ρ0) (mt))}])
                (proc-with-arity? f (length xs))}]
              [_ (if (op? u) ; primitive op handles arity check on its own
                     (s-map (λ (cl) (cek ms cl κ)) (δ u xs l))
                     {set (cek ms (close (blame/ l '∆) ρ0) (mt))})])]
           [(mon-fn-cl h f g (contract-cl (func-c cs1 c2) ρc) clo1)
            (if (= (length xs) (length cs1))
                (s-map
                 (match-lambda
                   [#t (cek ms clo1
                            (mon-ap-k
                             '() xs (map (λ (c) (close-contract c ρc)) cs1) h g f
                             (mon-k ; monitor result
                              h f g (close-contract c2 (env-extendl xs ρc)) κ)))]
                   [#f (cek ms (close (blame/ f h) ρ0) (mt))])
                 (proc-with-arity? clo1 (length cs1)))
                {set (cek ms (close (blame/ l h) ρ0) (mt))})]
           [_ {set (cek ms (close (blame/ l '∆) ρ0) (mt))}]))]
      [(if-k clo1 clo2 κ)
       (s-map (λ (v)
                (cek ms (match (val-pre (exp-cl-exp v)) [#t clo1] [#f clo2]) κ))
              (δ 'true? (list clo) '†))]
      [(mon-k h f g con-cl κ)
       (match-let ([(contract-cl c ρc) con-cl])
         (match (maybe-FC empty c)
           [`(,pred)
            {set
             (match (verify clo con-cl)
               ['Proved (cek ms clo κ)]
               ['Refuted (cek ms (close (blame/ f h) ρ0) (mt))]
               ['Neither
                (cek ms (close pred ρc)
                     (ap-k '() `(,clo) h #|TODO: is h the right label?|#
                           (if-k (refine clo con-cl)
                                 (close (blame/ f h) ρ0) κ)))])}]
           [`()
            (match c
              [(func-c cs1 c2)
               (s-map (λ (r) (match (val-pre (exp-cl-exp r))
                               [#t (cek ms (mon-fn-cl h f g con-cl clo) κ)]
                               [#f (cek ms (close (blame/ f h) ρ0) (mt))]))
                      (δ 'proc? `(,clo) '†))]
              [(cons-c c1 c2)
               ;; TODO: - more general when the language is uptyped
               ;;       - refactor with δ or something
               (s-map
                (match-lambda
                  [`(,cl1 ,cl2)
                   (cek ms cl1 (mon-k h f g (close-contract c1 ρc)
                                      (cdr-k h f g (close-contract c2 ρc) cl2 κ)))]
                  ['() (cek ms (exp-cl (blame/ f h) ρ0) (mt))])
                (split-cons clo))]
              [(or-c c1 c2)
               {set
                (match (verify clo (close-contract c1 ρc))
                  ['Proved (cek ms clo κ)]
                  ['Refuted (cek ms clo (mon-k h f g (close-contract c2 ρc) κ))]
                  ['Neither
                   (match (maybe-FC empty c1)
                     [`(,pred)
                      (cek ms (close pred ρc)
                           (ap-k '() `(,clo) h #|TODO: is h the right label?|#
                                 (or-k clo (close-contract c1 ρc)
                                       h f g (close-contract c2 ρc) κ)))]
                     [`() (error "left disjunction is not flat: " c1)])])}]
              [(and-c c1 c2)
               {set (cek ms clo
                         (mon-k h f g (close-contract c1 ρc)
                                (mon-k h f g (close-contract c2 ρc) κ)))}]
              [(rec-c c1)
               {set (cek clo 
                         (mon-k h f g
                                (close-contract c1 (env-extend con-cl ρc)) κ))}]
              [(ref-c x)
               {set (cek ms clo (mon-k h f g (env-get x ρc) κ))}])]))]
      [(cdr-k h f g c clo1 κ)
       {set (cek ms clo1
                 (mon-k h f g c
                        (ap-k `(,clo ,(close (val 'cons ∅) ρ0)) '()
                              h #|TODO: h, right label?|# κ)))}]
      [(or-k clo1 c1 h f g c2 κ)
       (s-map (λ (r)
                (match (val-pre (exp-cl-exp r))
                  [#t (cek ms (refine clo1 c1) κ)]
                  [#f (cek ms clo1 (mon-k h f g c2 κ))]))
              (δ 'true? `(,clo) h))]
      [(mon-ap-k vs (cons x xs) (cons c cs) h g f κ)
       {set
        (cek ms x (mon-k
                   h g f c
                   (mon-ap-k (cons clo vs) xs cs h g f κ)))}]
      [(mon-ap-k vs '() '() h g f κ)
       {set (cek ms clo (ap-k vs '() f κ))}]))
  
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
    (match-let ([(cek _ clo κ) conf])
      (and (mt? κ)
           (or (cons-cl? clo)
               (mon-fn-cl? clo)
               (answer? (exp-cl-exp clo))))))
  
  ;; run : CEK -> [Setof CEK]
  (define (run conf)
    ;; go : [Setof CEK] [Setof CEK] [Setof CEK] -> [Setof CEK]
    ;; INVARIANT:
    ;; -- known: states whose next states are explored
    ;; -- unknown: non-final states whose next states are unexplored
    ;; -- final: final states (~ answers)
    (define (go known unknown final)
      (cond
        [(set-empty? unknown) final]
        [else
         (define next (non-det step unknown))
         (define known1 (set-union known unknown))
         (define-values (final1 non-final1) (set-partition final? next))
         (go known1
             (set-subtract non-final1 known1)
             (set-union final final1))]))
    (go ∅ {set conf} ∅))
  
  ;; get-answer : Closure -> EvalAnswer
  (define (get-answer clo)
    (match clo
      [(exp-cl e ρ)
       (match e
         [(val u cs) (match u
                       [(lam n b) 'function]
                       ['• '•]
                       [u (if (op? u) 'function u)])]
         [(blame/ l1 l2) `(blame ,l1 ,l2)])]
      [(mon-fn-cl h f g conclo clo) 'function]
      [(cons-cl cl1 cl2) `(cons ,(get-answer cl1) ,(get-answer cl2))]))
  
  (s-map (compose get-answer cek-clo) (run (load (read-prog p)))))

;; verify : Closure ContractClosure -> Verified
;; Verified := 'Proved | 'Refuted | 'Neither
(define (verify clo conclo)
  (match clo
    [(exp-cl (val u cs) ρ) (if (set-member? cs conclo) 'Proved 'Neither)]
    [else 'Neither #|TODO|#]))

;;;; set helper functions

;; set-partition : (x -> Boolean) [Setof x] -> (Setof x) (Setof x)
(define (set-partition p? xs)
  (for/fold ([p-true ∅] [p-false ∅]) ([x (in-set xs)])
    (if (p? x)
        (values (set-add p-true x) p-false)
        (values p-true (set-add p-false x)))))

;; maybe-FC : [Listof Natural] Contract -> [List Exp] or Empty
;; converts flat contract to predicate
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