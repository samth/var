#lang racket
(provide
 opaque)

;; opaque : S-exp -> S-exp
(define opaque
  (match-lambda
    [`(module ,name
        (provide ,decls ...)
        (require ,reqs ...)
        ,defn ...)
     `(module ,name
        (provide ,@ decls)
        (require ,@ reqs)
        ,@ (map
            (match-lambda
              [`(,x ,c) `(define ,x •)])
            decls))]
    [`(module ,name
        (provide ,decls ...)
        ,defn ...)
     (opaque `(module ,name
                (provide ,@ decls)
                (require)
                ,@ defn))]))
  