#lang var cesk

(define-contract posn/c (struct/c posn exact-nonnegative-integer? exact-nonnegative-integer?))
(define-contract direction/c (one-of/c 'up 'down 'left 'right))
(define-contract snake/c
  (struct/c snake
            direction/c
            (non-empty-listof posn/c)))
(define-contract world/c
  (struct/c world
            snake/c
            posn/c))

(module data racket
  (struct posn (x y))
  (struct snake (dir segs))
  (struct world (snake food))

  ;; posn=? : Posn Posn -> Boolean
  ;; Are the posns the same?
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2))))

  (provide/contract
   [posn (exact-nonnegative-integer? exact-nonnegative-integer? . -> . posn/c)]
   [posn? (any/c . -> . boolean?)]
   [posn-x (posn/c . -> . exact-nonnegative-integer?)]
   [posn-y (posn/c . -> . exact-nonnegative-integer?)]
   [posn=? (posn/c posn/c . -> . boolean?)]
   [snake (direction/c (cons/c posn/c (listof posn/c)) . -> . snake/c)]
   [snake? (any/c . -> . boolean?)]
   [snake-dir (snake/c . -> . direction/c)]
   [snake-segs (snake/c . -> . (non-empty-listof posn/c))]
   [world (snake/c posn/c . -> . world/c)]
   [world? (any/c . -> . boolean?)]
   [world-snake (world/c . -> . snake/c)]
   [world-food (world/c . -> . posn/c)]))

(module D racket
  (require 'data)
  (provide/contract
   [f-posn ((exact-nonnegative-integer? exact-nonnegative-integer? . -> . posn/c) . -> . any/c)]
   [f-posn? ((any/c . -> . boolean?) . -> . any/c)]
   [f-posn-x ((posn/c . -> . exact-nonnegative-integer?) . -> . any/c)]
   [f-posn-y ((posn/c . -> . exact-nonnegative-integer?) . -> . any/c)]
   [f-posn=? ((posn/c posn/c . -> . boolean?) . -> . any/c)]
   [f-snake ((direction/c (cons/c posn/c (listof posn/c)) . -> . snake/c) . -> . any/c)]
   [f-snake? ((any/c . -> . boolean?) . -> . any/c)]
   [f-snake-dir ((snake/c . -> . direction/c) . -> . any/c)]
   [f-snake-segs ((snake/c . -> . (non-empty-listof posn/c)) . -> . any/c)]
   [f-world ((snake/c posn/c . -> . world/c) . -> . any/c)]
   [f-world? ((any/c . -> . boolean?) . -> . any/c)]
   [f-world-snake ((world/c . -> . snake/c) . -> . any/c)]
   [f-world-food ((world/c . -> . posn/c) . -> . any/c)]))

(require 'data 'D)

(begin
  (f-posn posn)
  (f-posn? posn?)
  (f-posn-x posn-x)
  (f-posn-y posn-y)
  (f-posn=? posn=?)
  (f-snake snake)
  (f-snake? snake?)
  (f-snake-dir snake-dir)
  (f-snake-segs snake-segs)
  (f-world world)
  (f-world? world?)
  (f-world-snake world-snake)
  (f-world-food world-food))