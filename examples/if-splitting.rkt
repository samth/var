#lang var
;; this doesn't work b/c we don't remember `cons?'
(module l racket
  (require)
  (define (f v)
    (if (cons? v) (first v) 7))
  (provide/contract [f (-> anything #;(rec/c X (or/c empty? (cons/c exact-nonnegative-integer? X))) anything)]))

(module m racket
  (provide/contract [ls anything #;(rec/c X (or/c empty? (cons/c exact-nonnegative-integer? X)))]))
(require (only-in l f) (only-in m ls))
(f ls)