#lang racket
(require racket/contract)

(provide
 (contract-out
  [s-map ((any/c . -> . any/c) (or/c set? list?) . -> . set?)]
  [non-det ((any/c . -> . set?) (or/c set? list?) . -> . set?)])
 non-det:)

(define ∅ (set))

;; maps function over set/list
(define (s-map f xs)
  (for/fold ([acc ∅]) ([x xs])
    (set-add acc (f x))))

;; non-deterministically applies function
(define (non-det f xs)
  (for/fold ([acc ∅]) ([x xs])
    (set-union acc (f x))))

;; syntactic abstraction for non-determinism
(define-syntax non-det:
  (syntax-rules (← return:)
    [(_ (X ← e) e1 e2 ...)
     (non-det
      (match-lambda
        [X (non-det: e1 e2 ...)]
        [_ ∅])
      e)]
    [(_ e1 e2 e3 ...) (begin e1 (non-det: e2 e3 ...))]
    [(_ (return: x ...)) {set x ...}]
    [(_ e) e]))