#lang racket
(require rackunit)
(require racket/contract)

(provide
 (contract-out
  [ρ0 env?] ; empty environment
  [env-extend (any/c env? . -> . env?)] ; TODO more precise
  [env-extendl ([listof any/c] env? . -> . env?)] ; TODO more precise
  [env-get (natural? env? . -> . any/c)] ; TODO more precise
  [env-get-default (natural? any/c env? . -> . any/c)] ; TODO more precise
  [env-has? (natural? env? . -> . boolean?)]
  [env-size (env? . -> . natural?)]
  [env-restrict ((set/c natural?) env? . -> . env?)]
  
  [env? (any/c . -> . boolean?)]
  [natural? (any/c . -> . boolean?)]
  ))

;; Env : think of it as a linked list whose index coincides with lexical
;; distance, but supports constant time accessing.
;; indices are stored in reverse internally, meaning hash[0] = env[farthest],
;; hash[size - 1] = env[nearest]

;; Env x = (env [HashTable Nat x] Nat)
(struct env (map size) #:transparent
  #:property
  prop:equal+hash
  ;; identifying environments up to irrelevant tails
  ;; e.g. [x,_,y] = [_,_,_,x,_,y]
  ;; otherwise examples like rsa-ap, sqrt-ap won't work
  (list (λ (a b equal?-recur)
          (match `(,a ,b)
            [`(,(env m1 s1) ,(env m2 s2)) (equal?-recur m1 m2)]))
        (λ (a hash-recur)
          (hash-recur (env-map a)))
        (λ (a hash2-recur)
          (hash2-recur (env-map a)))))

;; natural? : Any -> Boolean
(define (natural? x)
  (and (integer? x) (>= x 0)))

;; ρ0 : [Env x]
(define ρ0 (env (hash) 0))

;; env-extend : x [Env x] -> [Env x]
(define (env-extend x en)
  (match-let ([(env m s) en])
    (env (hash-set m s x) (+ 1 s))))

;; env-extendl : [Listof x] [Env x] -> [Env x]
(define (env-extendl xs en)
  (match xs
    [(cons x xs1) (env-extendl xs1 (env-extend x en))]
    ['() en]))

;; env-restrict : [Setof Natural] [Env x] -> [Env x]
;; restricts the environment to given set of distances.
(define (env-restrict ds en)
  ;; TODO: more efficient way?
  (match en
    [(env m s) (env (for/fold ([m1 (hash)]) ([d (in-set ds)])
                      (let ([i (- s 1 d)])
                        (if (hash-has-key? m i)
                            (hash-set m1 i (hash-ref m i))
                            m1)))
                    s)]))

;; env-get : Natural [Env x] -> x
;; returns element at given distance; raises error if there's nothing
(define (env-get d en)
  (if (env-has? d en)
      (hash-ref (env-map en) (- (env-size en) 1 d))
      (error "Nothing at distance " d)))

;; env-has? : Natural [Env x] -> Boolean
(define (env-has? d en)
  (hash-has-key? (env-map en) (- (env-size en) 1 d)))

;; env-get-default : Natural x [Env x] -> x
;; returns element at given distance, or default value if there's nothing
(define (env-get-default d def en)
  (if (env-has? d en) (env-get d en) def))

;; tests
(define closures `(3 2 1 0))
(define e (foldl env-extend ρ0 closures))
(for-each (λ (distance)
            (check-equal? distance (env-get distance e)))
          closures)

(define e1 (env-restrict (set 0 2) e))
(check-equal? (env-size e1) (env-size e))
(check-equal? (env-get-default 0 #f e1) 0)
(check-equal? (env-get-default 1 #f e1) #f)
(check-equal? (env-get-default 2 #f e1) 2)
(check-equal? (env-get-default 3 #f e1) #f)

(define e2 (env-restrict (set) e))
(check-equal? (env-size e2) (env-size e))
(check-equal? (env-get-default 0 #f e2) #f)
(check-equal? (env-get-default 1 #f e2) #f)
(check-equal? (env-get-default 2 #f e2) #f)
(check-equal? (env-get-default 3 #f e2) #f)