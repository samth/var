#lang racket

(require rackunit)
(require racket/contract)
(require "scpcf-lang.rkt")
(require "env.rkt")

(provide
 (contract-out
  [load (exp? . -> . cek?)]
  [step (cek? . -> . (set/c cek?))]
  [eval-cek (s-exp? . -> . (set/c eval-answer?))]
  
  [eval-answer? (any/c . -> . boolean?)]))

;; CEK = (cek Closure Kont)
(struct cek (clo kont) #:transparent)

;; Kont = Mt
;;      | Ar Closure Kont
;;      | Fn Closure Kont
;;      | If Closure Closure Kont
;;      | O Op [Listof Closure] [Listof Exp] Env Kont
;;      | Mon Label Label Label ContractClosure Kont
;;      | ChkCdr Label Label Label ContractClosure Closure Kont
;;      | ChkOr Closure Label Label Label ContractClosure Kont
(struct kont () #:transparent)
(struct mt kont () #:transparent)
(struct ar kont (clo k) #:transparent)
(struct fn kont (clo k) #:transparent)
(struct if/k kont (then else k) #:transparent)
(struct op/k kont (o vals exps env k) #:transparent)
(struct mon/k kont (h f g con-clo k) #:transparent)
; ad-hoc frames for checking cdr of a pair, and right disjunction
(struct chk-cdr kont (h f g con-clo clo k) #:transparent)
(struct chk-or kont (checked-clo con1 h f g con2 k) #:transparent)

;; load : Exp -> CEK
(define (load e)
  (cek (close e ρ0) (mt)))

;; step : CEK -> [Setof CEK]
(define (step conf)
  
  ;; refine : Closure ContractClosure -> Val
  (define (refine clo conclo)
    (match clo
      [(exp-clo (val u cs) ρ) (exp-clo (val u (set-add cs conclo)) ρ)]
      [else clo #|TODO|#]))
  
  ;; havoc : (FuncType | BaseType) -> Exp
  (define (havoc t)
    (match t
      [(func-type tx ty)
       (lam t (app (havoc ty) (app (ref 0) (val (opaque tx) {set}))))]
      [else (rec 'Num (ref 0))]))
  
  ;; on-nonval : Closure Kont -> [Setof CEK]
  (define (on-nonval clo κ)
    (let ([e (exp-clo-exp clo)]
          [ρ (exp-clo-env clo)])
      {set
       (match e
         [(ref x) (cek (env-get x ρ) κ)]
         [(blame/ f h) (cek (close e ρ0) (mt))]
         [(app e1 e2) (cek (close e1 ρ) (ar (close e2 ρ) κ))]
         [(rec t b) (cek (close b (env-extend clo ρ)) κ)]
         [(if/ e1 e2 e3)
          (cek (close e1 ρ) (if/k (close e2 ρ) (close e3 ρ) κ))]
         [(prim-app o (cons x xs)) (cek (close x ρ) (op/k o '[] xs ρ κ))]
         [(mon h f g c e1)
          (cek (close e1 ρ) (mon/k h f g (close-contract c ρ) κ))])}))
  
  ;; on-val : Closure Kont -> [Setof CEK]
  (define (on-val clo κ)
    (match κ
      [(mt) {set conf}]
      [(ar clo1 κ) {set (cek clo1 (fn clo κ))}]
      [(fn clo1 κ)
       (match clo1
         [(exp-clo (val u cs) ρv)
          (match u
            [(lam t b) {set (cek (close b (env-extend clo ρv)) κ)}]
            [(opaque (func-type tx ty))
             {set
              (cek (close (val (opaque ty)
                               (s-map (λ (c)
                                        (match c
                                          [(contract-clo (func/c c1 t c2) ρc)
                                           (close-contract c2 (env-extend clo ρc))]))
                                      cs))
                          ρ0)
                   κ)
              (cek (close (havoc tx) ρ0) (ar clo κ))}])]
         [(mon-fn-clo h f g (contract-clo (func/c c1 t c2) ρc) clo1)
          ;; break into 3 simpler frames
          {set
           (cek clo
                (mon/k ; monitor argument
                 h g f (close-contract c1 ρc)
                 (fn ; apply function
                  clo1
                  (mon/k ; monitor result
                   h f g (close-contract c2 (env-extend clo ρc)) κ))))}])]
      [(if/k clo1 clo2 κ)
       (s-map (λ (v)
                (cek (if (val-pre (exp-clo-exp v)) clo1 clo2) κ))
              (δ 'true? (list clo)))]
      [(op/k o vs es ρ κ)
       (match es
         [(cons e1 es1)
          {set (cek (close e1 ρ)
                    (op/k o (cons clo vs) es1 ρ κ))}]
         [empty
          (s-map (λ (a) (cek a κ))
                 (δ o (reverse (cons clo vs))))])]
      [(mon/k h f g (contract-clo c ρc) κ)
       (match (maybe-flatten empty c)
         [`(,pred)
          (match (verify clo (contract-clo c ρc))
            ['Proved {set (cek clo κ)}]
            ['Refuted {set (close (blame/ f h) ρ0) (mt)}]
            ['Neither
             {set (cek (close pred ρc)
                       (ar clo
                           (if/k (refine clo (contract-clo c ρc))
                                 (close (blame/ f h) ρ0) κ)))}])]
         [`()
          (match c
            [(func/c c1 t c2)
             {set (cek (mon-fn-clo h f g (contract-clo c ρc) clo) κ)}]
            [(consc c1 c2)
             ;; TODO: - more general when the language is uptyped
             ;;       - refactor with δ or something
             (match clo
               [(cons-clo car1 cdr1)
                {set
                 (cek car1 (mon/k
                            h f g (close-contract c1 ρc)
                            (chk-cdr
                             h f g (close-contract c2 ρc) cdr1 κ)))}]
               [(exp-clo (val (opaque (list-type t)) cs) ρ1)
                {set
                 (cek (val (opaque t) ∅)
                      (mon/k h f g (close-contract c1 ρc)
                             (chk-cdr
                              h f g (close-contract c2 ρc)
                              (val (opaque (list-type t)) ∅) κ)))
                 (cek (close (blame/ f h) ρ0) (mt))}]
               [_ {set (cek (close (blame/ f h) ρ0) (mt))}])]
            [(orc c1 c2)
             (match (verify clo (close-contract c1 ρc))
               ['Proved {set (cek clo κ)}]
               ['Refuted
                {set (cek clo (mon/k h f g (close-contract c2 ρc) κ))}]
               ['Neither
                (match (maybe-flatten empty c1)
                  [`(,pred)
                   {set
                    (cek (close pred ρc)
                         (ar clo
                             (chk-or clo (close-contract c1 ρc)
                                     h f g (close-contract c2 ρc) κ)))}]
                  [`() (error "First contract disjunction is not flat" c1)])])]
            [(andc c1 c2)
             {set (cek clo
                       (mon/k h f g (close-contract c1 ρc)
                              (mon/k h f g (close-contract c2 ρc) κ)))}]
            [(rec/c t c1)
             {set (cek clo 
                       (mon/k h f g
                              (close-contract c1 (env-extend c ρc)) κ))}]
            [(con-ref x)
             {set (cek clo (mon/k h f g (env-get x ρc) κ))}])])]
      
      [(chk-cdr h f g c clo1 κ)
       {set (cek clo1 (mon/k h f g c
                             (op/k 'cons `(,clo) '() ρ0 κ)))}]
      [(chk-or clo1 c1 h f g c2 κ)
       (s-map (λ (r)
                (if (val-pre (exp-clo-exp r))
                    (cek (refine clo1 c1) κ)
                    (cek clo1 (mon/k h f g c2 κ))))
              (δ 'true? `(,clo)))]))
  
  (match-let ([(cek clo kont) conf])
    (if (val-closure? clo)
        (on-val clo kont)
        (on-nonval clo kont))))

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
(define (eval-cek e)
  
  ;; final? : CEK -> Boolean
  (define (final? conf)
    (and (mt? (cek-kont conf))
         (or (cons-clo? (cek-clo conf))
             (mon-fn-clo? (cek-clo conf))
             (answer? (exp-clo-exp (cek-clo conf))))))
  
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
      [(exp-clo e ρ)
       (match e
         [(val u cs) (match u
                       [(lam t b) 'function]
                       [(opaque (func-type tx ty)) 'function]
                       [(opaque t) '•]
                       [u u])]
         [(blame/ l1 l2) `(blame ,l1 ,l2)])]
      [(mon-fn-clo h f g conclo clo) 'function]
      [(cons-clo cl1 cl2) `(cons ,(get-answer cl1) ,(get-answer cl2))]))
  
  (s-map (compose get-answer cek-clo) (run (load (read-exp e)))))

;; verify : Closure ContractClosure -> Verified
;; Verified := 'Proved | 'Refuted | 'Neither
(define (verify clo conclo)
  (match clo
    [(exp-clo (val u cs) ρ) (if (set-member? cs conclo) 'Proved 'Neither)]
    [else 'Neither #|TODO|#]))

;; non-det : (x -> [Setof y]) [Setof x] -> [Setof y]
(define (non-det f xs)
  (apply set-union (set-map xs f)))


;;;; set helper functions

;; s-map : [x -> y] [Setof x] -> [Setof y]
(define (s-map f xs)
  #;(for/set ([x xs]) (f x))
  ; TODO: is this how I use in-set?
  (for/fold ([ys ∅]) ([x (in-set xs)]) (set-add ys (f x))))

;; set-partition : (x -> Boolean) [Setof x] -> (Setof x) (Setof x)
(define (set-partition p? xs)
  (for/fold ([p-true ∅] [p-false ∅]) ([x (in-set xs)])
    (if (p? x)
        (values (set-add p-true x) p-false)
        (values p-true (set-add p-false x)))))

;; maybe-flatten : [Listof Natural] Contract -> [List Exp] or Empty
;; converts flat contract to predicate
;; whether result expression is closed or open depends on original contract
;; -- ds: (list-ref ds k) is number of extra levels of λ introduced
;;        after the k-th (μ.C)
(define (maybe-flatten ds c)
  
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
    [(flat/c p) (list (shift (apply + ds) p))]
    [(func/c c t d) empty]
    [(consc c1 c2) (lift (λ (p1 p2)
                           (val (lam '⊥ ; program already type-checked
                                     (and/ (prim-app 'cons (ref 0))
                                           (app p1 (prim-app 'car (ref 0)))
                                           (app p2 (prim-app 'cdr (ref 0)))))
                                ∅))
                         (maybe-flatten (car+1 ds) c1)
                         (maybe-flatten (car+1 ds) c2))]
    [(orc c1 c2) (lift (λ (p1 p2)
                         (val (lam '⊥ ; program already type-checked
                                   (or/ (app p1 (ref 0))
                                        (app p2 (ref 0))))
                              ∅))
                       (maybe-flatten (car+1 ds) c1)
                       (maybe-flatten (car+1 ds) c2))]
    [(andc c1 c2) (lift (λ (p1 p2)
                          (val (lam '⊥ ; program already type-checked
                                    (and/ (app p1 (ref 0))
                                          (app p2 (ref 0))))
                               ∅))
                        (maybe-flatten (car+1 ds) c1)
                        (maybe-flatten (car+1 ds) c2))]
    [(rec/c (con-type t) c1) (lift (λ (e) (rec (func-type t 'Bool) e))
                                   (maybe-flatten (cons 0 ds) c1))]
    [(con-ref x) (list (ref (+ (car ds) x)))]))
