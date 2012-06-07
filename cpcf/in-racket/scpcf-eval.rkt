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
;;      | O Op [Listof Value] [Listof Exp] Env Kont
;;      | Mon Label Label Label ContractClosure Kont
;;      | Cons-car Closure Kont
;;      | Cons-cdr Closure Kont
;;      | Nil? Kont
;;      | Cons? Kont
;;      | Car Kont
;;      | Cdr Kont
(struct kont () #:transparent)
(struct mt kont () #:transparent)
(struct ar kont (clo k) #:transparent)
(struct fn kont (clo k) #:transparent)
(struct if/k kont (then else k) #:transparent)
(struct op/k kont (o vals exps env k) #:transparent)
(struct mon/k kont (h f g con-clo k) #:transparent)
(struct cons-car kont (clo k) #:transparent)
(struct cons-cdr kont (clo k) #:transparent)
(struct nil?/k kont (k) #:transparent)
(struct cons?/k kont (k) #:transparent)
(struct car/k kont (k) #:transparent)
(struct cdr/k kont (k) #:transparent)

;; load : Exp -> CEK
(define (load e)
  (cek (close e env-empty) (mt)))

;; step : CEK -> [Setof CEK]
(define (step conf)
  
  ;; refine : Closure ContractClosure -> Value
  (define (refine clo conclo)
    (match clo
      [(exp-clo (value u cs) ρ) (exp-clo (value u (set-add cs conclo)) ρ)]
      [else clo #|TODO|#]))
  
  ;; havoc : (FuncType | BaseType) -> Exp
  (define (havoc t)
    (match t
      [(func-type tx ty)
       (lam t (app (havoc ty) (app (ref 0) (value (opaque tx) {set}))))]
      [else (rec 'Num (ref 0))]))
  
  ;; nil-clo? : Closure -> [Setof Boolean]
  ;; (non-deterministically) checks whether closure represents nil
  (define (nil-clo? c)
    (match c
      [(exp-clo (value u cs) ρ) (match u
                                  ['nil {set #t}]
                                  [(opaque (list-type t)) {set #t #f}]
                                  [_ {set #f}])]
      [_ {set #f}]))
  
  ;; cons-clo?/ : Closure -> [Setof Boolean]
  ;; (non-deterministically) checks whther closure represents nil
  (define (cons-clo?/ c)
    (match c
      [(exp-clo (value (opaque (list-type t)) cs) ρ) {set #t #f}]
      [(cons-clo cl1 cl2) {set #t}]
      [_ {set #f}]))
  
  (match conf
    [(cek clo κ)
     (if (and (exp-clo? clo) (not (value? (exp-clo-exp clo))))
         (let ([e (exp-clo-exp clo)]
               [ρ (exp-clo-env clo)])
           {set
            (match e
              [(ref x) (cek (env-get x ρ) κ)]
              [(blame/ f h) (cek (close e env-empty) (mt))]
              [(app e1 e2) (cek (close e1 ρ) (ar (close e2 ρ) κ))]
              [(rec t b) (cek (close b (env-extend clo ρ)) κ)]
              [(if/ e1 e2 e3)
               (cek (close e1 ρ) (if/k (close e2 ρ) (close e3 ρ) κ))]
              [(prim-app o (cons x xs)) (cek (close x ρ) (op/k o '[] xs ρ κ))]
              [(mon h f g c e1)
               (cek (close e1 ρ) (mon/k h f g (close-contract c ρ) κ))]
              [(cons/ e1 e2) (cek (close e1 ρ) (cons-cdr (close e2 ρ) κ))]
              [(nil?/ e1) (cek (close e1 ρ) (nil?/k κ))]
              [(cons?/ e1) (cek (close e1 ρ) (cons?/k κ))]
              [(car/ e1) (cek (close e1 ρ) (car/k κ))]
              [(cdr/ e1) (cek (close e1 ρ) (cdr/k κ))])})
         ;; Cl = <V, ρ> | MonFnClo | ConsClo, all are 'values' in some sense
         ;; dispatch on kontinuation
         (match κ
           [(mt) {set conf}]
           [(ar clo1 κ) {set (cek clo1 (fn clo κ))}]
           [(fn clo1 κ)
            (match clo1
              [(exp-clo (value u cs) ρv)
               (match u
                 [(lam t b) {set (cek (close b (env-extend clo ρv)) κ)}]
                 [(opaque (func-type tx ty))
                  {set
                   (cek (close (value (opaque ty)
                                      (s-map (λ (c)
                                               (match c
                                                 [(contract-clo (func/c c1 t c2) ρc)
                                                  (close-contract c2 (env-extend clo ρc))]))
                                             cs))
                               env-empty)
                        κ)
                   (cek (close (havoc tx) env-empty) (ar clo κ))}])]
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
                     (cek (if (value-pre v) clo1 clo2) κ))
                   (δ 'true? (list (exp-clo-exp clo))))]
           [(op/k o vs es ρ κ)
            (match es
              [(cons e1 es1)
               {set (cek (close e1 ρ)
                         (op/k o (cons (exp-clo-exp clo) vs) es1 ρ κ))}]
              [empty
               (s-map (λ (a)
                        (cek (close a env-empty) κ))
                      (δ o (reverse (cons (exp-clo-exp clo) vs))))])]
           [(mon/k h f g conclo κ)
            {set
             (match (verify clo conclo)
               ['Proved (cek clo κ)]
               ['Refuted (cek (close (blame/ f h) env-empty) (mt))]
               ['Neither
                (match (contract-clo-con conclo)
                  [(flat/c p)
                   (cek (close p (contract-clo-env conclo))
                        (ar clo
                            (if/k (refine clo conclo)
                                  (close (blame/ f h) env-empty) κ)))]
                  [(func/c c1 t c2) (cek (mon-fn-clo h f g conclo clo) κ)])])}]
           [(cons-car clo1 κ) {set (cek (cons-clo clo1 clo) κ)}]
           [(cons-cdr clo1 κ) {set (cek clo1 (cons-car clo κ))}]
           [(nil?/k κ) (s-map (λ (b)
                                (cek (close (value b ∅) env-empty) κ))
                              (nil-clo? clo))]
           [(cons?/k κ) (s-map (λ (b)
                                 (cek (close (value b ∅) env-empty) κ))
                               (cons-clo?/ clo))]
           [(car/k κ)
            {set (match clo
                   [(cons-clo clo1 _) (cek clo1 κ)]
                   #|TODO opaque|#
                   [else (cek (close (blame/ '† 'car) env-empty) κ)])}]
           [(cdr/k κ)
            {set (match clo
                   [(cons-clo _ clo2) (cek clo2 κ)]
                   #|TODO opaque|#
                   [else (cek (close (blame/ '† 'cdr) env-empty) κ)])}]))]))

;; EvalAnswer := Number | Boolean | '• | '(blame Label Label)
;;            | 'function
;; eval-answer? : Any -> Boolean
(define (eval-answer? x)
  (match x
    [`(blame ,l1 ,l2) (and (symbol? l1) (symbol? l2))]
    [else (or (number? x) (boolean? x) (member x `(function •)))]))

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
         [(value u cs) (match u
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
    [(exp-clo (value u cs) ρ) (if (set-member? cs conclo) 'Proved 'Neither)]
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

;; for debugging
(define step1 (curry non-det step))
(define (pow f n) (apply compose (make-list n f)))
(define (step* k e) ((pow step1 k) (set (load (read-exp e)))))

;;;;; tests
(check-equal? (eval-cek ev?) {set 'function})
(check-equal? (eval-cek ap00) {set 2})
(check-equal? (eval-cek ap01) {set `(blame g h)})
(check-equal? (eval-cek `(,tri 3)) {set 6})
(check-equal? (eval-cek rsa-ap) {set `• `(blame f h)})
#;(check-equal? (eval-cek sqrt-ap) {set '• '(blame g h)})