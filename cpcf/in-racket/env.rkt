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
  [env-pop (env? (or/c symbol? [listof symbol?]) . -> . env?)]
  [env? (any/c . -> . boolean?)]
  
  [env-size (env? . -> . integer?)]
  [env-has? (env? symbol? . -> . any/c)]
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
(define (env-pop ρ x)
  (cond
    [(symbol? x) (hash-remove ρ x)]
    [else (foldl (λ (z ρ1) (hash-remove ρ1 z)) ρ x)]))

;; returns environment's domain size
;; env-size : env? -> nat?
(define env-size hash-count)

;; returns whether key is in environment's domain
(define env-has? hash-has-key?)
