#lang racket
(require rackunit)
(require racket/contract)

(provide
 (contract-out
  [env-empty env?]
  [env-extend (any/c env? . -> . env?)] ; TODO more precise
  [env-get (natural? env? . -> . any/c)] ; TODO more precise
  [env-get-default (natural? any/c env? . -> . any/c)] ; TODO more precise
  [env-has? (natural? env? . -> . boolean?)]
  [env-size (env? . -> . natural?)]
  
  [env? (any/c . -> . boolean?)]
  [natural? (any/c . -> . boolean?)]
  ))

;; Env : think of it as a linked list whose index coincides with lexical
;; distance, but supports constant time accessing.
;; indices are stored in reverse internally, meaning hash[0] = env[farthest],
;; hash[size - 1] = env[nearest]

;; env? : Any -> Boolean
(define env? hash?)

;; natural? : Any -> Boolean
(define (natural? x)
  (and (integer? x) (>= x 0)))

;; env-empty : [Env x]
(define env-empty (hash))

;; env-extend : x [Env x] -> [Env x]
(define (env-extend x env)
  (hash-set env (env-size env) x))

;; env-size : [Env x] -> Natural
(define env-size hash-count)

;; env-get : Natural [Env x] -> x
;; returns element at given distance; raises error if there's nothing
(define (env-get distance env)
  (if (env-has? distance env)
      (hash-ref env (- (env-size env) 1 distance))
      (error "Nothing at distance " distance)))

;; env-has? : Natural [Env x] -> Boolean
(define (env-has? distance en)
  (< distance (env-size en)))

;; env-get-default : Natural x [Env x] -> x
;; returns element at given distance, or default value if there's nothing
(define (env-get-default distance def env)
  (if (env-has? distance env) (env-get distance env) def))


;; tests
(define closures `(3 2 1 0))
(define e (foldl env-extend env-empty closures))
(for-each (λ (distance)
            (check-equal? distance (env-get distance e)))
          closures)