#lang racket

(require rackunit)
(require racket/contract)
(require "scpcf-lang.rkt")
(require "env.rkt")

(provide
 (contract-out
  [load (exp? . -> . cek?)]
  [step (cek? . -> . (set/c cek?))]))

;; CEK = (cek Exp [Env Value] Kont)
(struct cek (exp env kont) #:transparent)

;; Kont = Mt
;;      | Ar Exp Env Kont
;;      | Fn Value Env Kont
;;      | If Exp Exp Env Kont
;;      | O Op [Listof Value] [Listof Exp] Env Kont
;;      | Mon Label Label Label Contract Env Kont
;;      | MonFn Label Label Label Contract Contract Env Value Env Kont
(struct kont () #:transparent)
(struct mt kont () #:transparent)
(struct ar kont (e env k) #:transparent)
(struct fn kont (body env k) #:transparent)
(struct if/k kont (then else env k) #:transparent)
(struct op/k kont (o vals exps env k) #:transparent)
(struct mon/k kont (h f g con env k) #:transparent)

(struct mon-fn kont (h f g c1 c2 con-env body env k))
;; c1: contract for domain
;; c2: contract for range, originally under λ
;; con-env: environment that closes c1 and (λ.c2)
;; body: the pending function's body
;; env: environment that closes (λ.body)

;; load : Exp -> CEK
(define (load e)
  (cek e env-empty (mt)))

;; step : CEK -> [Setof CEK]
(define (step conf)
  
  ;; s-map : [x -> y] [Setof x] -> [Setof y]
  (define (s-map f xs)
    (list->set (set-map xs f)))
  
  ;; refine : Value ContractClosure -> Value
  (define (refine v c)
    (value (value-pre v) (set-add (value-refinements v) c)))
  
  ;; havoc : (FuncType | BaseType) -> Exp
  (define (havoc t)
    (match t
      [(func-type tx ty)
       (lam t (app (havoc ty) (app (ref 0) (value (opaque tx) {set}))))]
      [else (rec 'Int (ref 0))]))
  
  (match conf
    
    ;; application
    [(cek [app e1 e2] ρ κ) {set (cek e1 ρ [ar e2 ρ κ])}] ; (e e) -> ([] e)
    [(cek [value u cs] ρ1 [ar e ρ2 κ]) ; (v e) -> (v [])
     {set (cek e ρ2 [match u
                      [(mon-lam h f g (func/c c1 t c2) ρc u1)
                       (mon-fn h f g c1 c2 ρc (value u1 cs) ρ1 κ)]
                      [else (fn (value u cs) ρ1 κ)]])}]
    [(cek [value u cs] ρ2 [fn (value (lam t e) _) ρ1 κ]) ; (fn v)
     {set (cek e [env-extend (clo (value u cs) ρ2) ρ1] κ)}]
    [(cek [value u cs] ρv [mon-fn h f g c1 c2 ρc fun ρb κ])
     {set (cek [value u cs] ρv ;; manually add 3 frames:
               [mon/k h g f c1 ρc ;; (1) monitor the argument
                      [fn fun ρb ;; (2) apply the function
                          ;; (3) monitor the result
                          [mon/k h f g c2 (env-extend (clo (value u cs) ρv) ρc)
                                 κ]]])}]
    [(cek [value u cs2] ρv [fn (value (opaque (func-type t1 t2)) cs1) ρ κ])
     {set (cek [value
                (opaque t2)
                {s-map (λ (c)
                         (let ([d (func/c-rng c)])
                           (contract-clo
                            d
                            (env-extend (clo (value u cs2) ρv) ρ))))
                       cs1}]
               env-empty κ)
          (cek [app (havoc t1) [value u cs2]] env-empty κ)}]
    
    ;; μ
    [(cek [rec t e] ρ κ) {set (cek e [env-extend (clo (rec t e) ρ) ρ] κ)}]
    
    ;; if
    [(cek [if/ e1 e2 e3] ρ κ) {set (cek e1 ρ [if/k e2 e3 ρ κ])}]
    [(cek [value u cs] ρ1 [if/k e2 e3 ρ κ])
     {s-map (λ (v)
              (cek [if (value-pre v) e2 e3] ρ κ))
            (δ 'true? (list (value u cs)))}]
    
    ;; primitive ops
    [(cek [prim-app o (cons x xs)] ρ κ) {set (cek x ρ [op/k o '() xs ρ κ])}]
    [(cek [value u cs] ρv [op/k o vs (cons x xs) ρ κ])
     {set (cek x ρ [op/k o (cons (value u cs) vs) xs ρ κ])}]
    [(cek [value u cs] ρv [op/k o vs '() ρ κ])
     {s-map (λ (v) (cek v env-empty κ))
            (δ o (reverse (cons (value u cs) vs)))}]
    
    ;; monitored expression
    [(cek [mon h f g c e] ρ κ) {set (cek e ρ [mon/k h f g c ρ κ])}]
    [(cek [value u cs] ρv [mon/k h f g c ρc κ])
     {set (match (verify (value u cs) (contract-clo c ρc))
            ['Proved (cek [value u cs] ρv κ)]
            ['Refuted (cek [blame/ f h] env-empty κ)]
            ['Neither
             (match c
               [(flat/c e)
                ;; add 2 kont frames manually
                (cek e ρc [ar (value u cs) ρv
                              [if/k (refine (value u cs) (contract-clo c ρc))
                                    (blame/ f h)
                                    ρv
                                    κ]])]
               [(func/c dom t rng)
                ;; convert monitored function to special closure used internally
                (cek [value (mon-lam h f g c ρc u) cs] ρv κ)])])}]
    
    ;; is it ok to do this?
    [(cek [blame/ f h] ρ κ) {set (cek [blame/ f h] env-empty (mt))}]
    
    ;; retain value
    [(cek [value u cs] ρ (mt)) {set conf}]
    
    ;; variable encoded as lexical distance
    [(cek (ref d) ρ κ) (let ([clo (env-get d ρ)])
                         {set (cek [clo-exp clo] [clo-env clo] κ)})]))


;; verify : Value ContractClosure -> Verified
;; Verified := 'Proved | 'Refuted | 'Neither
(define (verify v c)
  (if (set-member? (value-refinements v) c) 'Proved 'Neither))

;; fix : (x -> x) x (x x -> Boolean) -> x
(define (fix f x =?)
  ;; go : x x -> x
  (define (go x y)
    (if (=? x y) x (go y (f y))))
  (go x (f x)))

;; non-det : (x -> [Setof y]) [Setof x] -> [Setof y]
(define (non-det f xs)
  (apply set-union (set-map xs f)))

;;;;; tests

;; TODO test evaluation
#;`([,ev? {,ev?} "ev?"]
    [,ap00 {2} "ap00"]
    [(,tri 3) {6} "tri"])

(define (run sexp steps)
  (let ([exp (read-exp sexp)])
    (match (type-check exp)
      ['TypeError (error "Does not type check")]
      [else (let ([m (load exp)])
              ((pow steps (curry non-det step)) {set m}))])))

(define (pow k f)
  (apply compose (make-list k f)))