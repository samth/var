#lang racket
(require rackunit)
(require racket/contract)

(provide
 (contract-out
  [env-empty (any/c . -> . env?)]
  [env-extend (any/c env? . -> . env?)] ; TODO more precise
  [env-get (natural? env? . -> . any/c)] ; TODO more precise
  [env-has? (natural? env? . -> . boolean?)]
  [env-size (env? . -> . natural?)]
  
  [natural? (any/c . -> . boolean?)]
  ))

;; Env : think of it as a linked list whose index coincides with lexical
;; distance, but supports constant time accessing.
;; indices are stored in reverse internally, meaning hash[0] = env[farthest],
;; hash[size - 1] = env[nearest]

;; Env x = (env (Hash Natural x) x)
(struct env (map default))

;; natural? : Any -> Boolean
(define (natural? x)
  (and (integer? x) (>= x 0)))

;; env-empty : x -> [Env x]
(define (env-empty default)
  (env (hash) default))

;; env-extend : x [Env x] -> [Env x]
(define (env-extend x en)
  (let ([map (env-map en)]
        [new-pos (env-size en)])
    (env (hash-set map new-pos x) (env-default en))))

;; env-size : [Env x] -> Natural
(define env-size (compose hash-count env-map))

;; env-get : Natural [Env x] -> x
;; returns element at given distance, or default value on invalid distance
(define (env-get distance en)
  (if (env-has? distance en)
      (hash-ref (env-map en) (- (env-size en) 1 distance))
      (env-default en)))

;; env-has? : Natural [Env x] -> Boolean
(define (env-has? distance en)
  (< distance (env-size en)))


;; tests
(define closures `(3 2 1 0))
(define e (foldl env-extend (env-empty 'not-found) closures))
(for-each (λ (distance)
            (check-equal? distance (env-get distance e)))
          closures)