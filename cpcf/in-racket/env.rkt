#lang racket
(require rackunit)
(require racket/contract)

(provide
 (contract-out
  [env0 env?]
  [env+ (env? symbol? any/c . -> . env?)]
  [env++ (env? [listof (list symbol any/c)] . -> . env?)]
  [env-get (env? symbol? . -> . any/c)]
  [env-set (env? symbol? any/c . -> . env?)]
  [env-upd (env? symbol? (any/c . -> . any/c) . -> . env?)]
  [env-restrict (env? (set/c symbol?) . -> > env?)]
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
  (let loop ([ρ ρ] [kvs])
    (match kvs
      ['() ρ]
      [(cons `(,k ,v) kvs′) (loop (env+ ρ k v) kvs′)])))

;; looks up environment
(define env-get hash-ref)

;; updates environment with given function
(define env-upd hash-update)

;; defined in terms of env-upd instead of hash-set for domain check
(define (env-set ρ k v) (env-upd ρ k (cons v)))

;; removes key from environment's domain
(define env-pop hash-remove)