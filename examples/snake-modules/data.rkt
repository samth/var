#lang var rho
(module data racket 
  (struct posn (x y))
  (struct snake (dir segs))
  (struct world (snake food))
  
  ;; direction? : Any -> Boolean
  ;; Is s a direction?
  (define (direction? s)
    (and (string? s)
         (or (string=? s "up")
             (string=? s "down")
             (string=? s "left")
             (string=? s "right"))))
  
  ;; posn=? : Posn Posn -> Boolean
  ;; Are the posns the same?
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2))))  
  
  (provide/contract 
   [direction? (any/c . -> . boolean?)]
   [posn (exact-nonnegative-integer? exact-nonnegative-integer? . -> . posn?)]
   [posn? (any/c . -> . boolean?)]
   [posn-x (posn? . -> . exact-nonnegative-integer?)]
   [posn-y (posn? . -> . exact-nonnegative-integer?)]
   [posn=? (posn? posn? . -> . boolean?)]
   [snake (direction? (cons/c posn? (listof posn?)) . -> . snake?)]
   [snake? (any/c . -> . boolean?)]
   [snake-dir (snake? . -> . direction?)]
   [snake-segs (snake? . -> . (non-empty-listof posn?))]
   [world (snake? posn? . -> . world?)]
   [world? (any/c . -> . boolean?)]
   [world-snake (world? . -> . snake?)]
   [world-food (world? . -> . posn?)]))

(module hole racket
  (provide/contract [f (any/c . -> . any/c)]))

;; We're losing a lot of information about structes.
;; For example, (-- (pred snake?)) tells you nothing about
;; the value.  (-- (s-pred data snake)) is what you want.
;; The annotator needs to change to expand structure predicates
;; to their underlying operations.

;; We're not doing demonic of structures right (ie, we don't do anything).

(require 'data 'hole)
(begin (f direction?)
       (f posn)
       (f posn?)
       (f posn-x)
       (f posn-y)
       (f posn=?)
       (f snake)
       (f snake?)
       (f snake-segs)
       (f world)
       (f world?)
       (f world-snake)
       (f world-food))