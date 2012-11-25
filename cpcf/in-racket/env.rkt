#lang racket
(require rackunit)
(require racket/contract)

(provide
 (contract-out
  [env0 env?]
  [env+ (env? symbol? any/c . -> . env?)]
  [env++ (env? [listof (list/c symbol? any/c)] . -> . env?)]
  [env-get (env? symbol? . -> . any/c)]
  [env-set (env? symbol? any/c . -> . env?)]
  [env-upd (env? symbol? (any/c . -> . any/c) . -> . env?)]
  [env-restrict (env? (set/c symbol?) . -> . env?)]
  [env-pop (env? symbol? . -> . env?)]
  
  [Γ-mk (env? env? . -> . env?)]
  [Γ-upd (env? env? . -> . env?)]
  
  [env? (any/c . -> . boolean?)]
  ))

;; predicate for environment type
(define env? hash?)

;; empty environmen
(define env0 (hash))

;; extends environment with given key-val pair
(define env+ hash-set)

;; extends environment with given key-val pairs
(define (env++ ρ kvs)
  (let loop ([ρ ρ] [kvs kvs])
    (match kvs
      ['() ρ]
      [(cons `(,k ,v) kvs′) (loop (env+ ρ k v) kvs′)])))

;; looks up environment
(define env-get hash-ref)

;; updates environment with given function
(define env-upd hash-update)

;; defined in terms of env-upd instead of hash-set for domain check
(define (env-set ρ k v) (env-upd ρ k (const v)))

;; restricts environment to given domain
(define (env-restrict ρ X)
  (if (< (hash-count ρ) (set-count X))
      (let ([ρ′ ρ])
        (hash-for-each ρ (λ (k v)
                           (when (not (set-member? X k))
                             (set! ρ′ (hash-remove ρ′ k)))))
        ρ′)
      (for/fold ([ρ′ env0]) ([x X])
        (if (hash-has-key? ρ x)
            (hash-set ρ′ x (hash-ref ρ x))
            ρ′))))

;; removes key from environment's domain
(define env-pop hash-remove)

;; returns environment's domain size
;; env-size : env? -> nat?
(define env-size hash-count)

;; returns whether key is in environment's domain
(define env-has? hash-has-key?)

;; makes proposition environment with given domain
;; that knows everything Γ knows
(define (Γ-mk dom Γ)
  (define fresh-Γ
    (cond
      [(env? dom) (let ([Γ′ env0])
                    (hash-for-each dom
                                   (λ (k v) (set! Γ′ (hash-set Γ′ k 'tt))))
                    Γ′)]
      [else (foldl (λ (x Γ′) (hash-set Γ′ x 'tt)) env0 dom)]))
  (Γ-upd fresh-Γ Γ))


;; updates Γ1 with all Γ2 knows
;; assume Γ2 knows no less than Γ1
(define (Γ-upd Γ1 Γ2)
  (if (< (env-size Γ1) (env-size Γ2))
      (hash-for-each Γ1 (λ (k _)
                          (when (hash-has-key? Γ2 k)
                            (set! Γ1 (hash-set Γ1 k (hash-ref Γ2 k))))))
      (hash-for-each Γ2 (λ (k v)
                          (when (hash-has-key? Γ1 k)
                            (set! Γ1 (hash-set Γ1 k v))))))
  Γ1)
