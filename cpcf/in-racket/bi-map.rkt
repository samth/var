#lang racket

(provide
 (contract-out
  [empty-bi-map bi-map?]
  [bi-map-set (bi-map? any/c any/c . -> . bi-map?)]
  [bi-map-get-val (bi-map? any/c . -> . any/c)]
  [bi-map-get-key (bi-map? any/c . -> . any/c)]
  [bi-map-del-key (bi-map? any/c . -> . bi-map?)]
  [bi-map-del-val (bi-map? any/c . -> . bi-map?)]
  [bi-map-has-key? (bi-map? any/c . -> . boolean?)]
  [bi-map-has-val? (bi-map? any/c . -> . boolean?)]
  
  [bi-map? (any/c . -> . boolean?)]))

(struct bi-map (k->v v->k) #:transparent)

(define empty-bi-map
  (bi-map (hash) (hash)))

;; bi-map-set : [BiMap K V] K V -> [BiMap K V]
(define (bi-map-set m k v)
  (match-let ([(bi-map k->v v->k) m])
    (bi-map (hash-set k->v k v) (hash-set v->k v k))))

;; bi-map-get-val : [BiMap K V] K -> V
(define (bi-map-get-val m k)
  (hash-ref (bi-map-k->v m) k))

;; bi-map-get-key : [BiMap K V] V -> K
(define (bi-map-get-key m v)
  (hash-ref (bi-map-v->k m) v))

;; bi-map-del-key : [BiMap K V] K -> [BiMap K V]
(define (bi-map-del-key m k)
  (if (bi-map-has-key? m k)
      (match-let* ([(bi-map k->v v->k) m]
                   [v (hash-ref k->v k)])
        (bi-map (hash-remove k->v k) (hash-remove v->k v)))
      m))

;; bi-map-del-val : [BiMap K V] V -> [BiMap K V]
(define (bi-map-del-val m v)
  (if (bi-map-has-val? m v)
      (match-let* ([(bi-map k->v v->k) m]
                   [k (hash-ref v->k v)])
        (bi-map (hash-remove k->v k) (hash-remove v->k v)))
      m))

;; bi-map-has-key? : [BiMap K V] K -> Boolean
(define (bi-map-has-key? m k)
  (hash-has-key? (bi-map-k->v m) k))

;; bi-map-has-val? : [BiMap K V] V -> Boolean
(define (bi-map-has-val? m v)
  (hash-has-key? (bi-map-v->k m) v))