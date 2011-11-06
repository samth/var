#lang var rho

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

(module cut-tail racket
  (require 'data)

  ;; NeSegs is one of:
  ;; - (cons Posn empty)
  ;; - (cons Posn NeSegs)

  ;; cut-tail : NeSegs -> Segs
  ;; Cut off the tail.
  (define (cut-tail segs)
    (let ([r (cdr segs)])
      (cond [(empty? r) empty]
            [else
             (cons (car segs)
                   (cut-tail r))])))

  (provide/contract [cut-tail ((non-empty-listof posn/c) . -> . (listof posn/c))]))

(module H racket
  (require 'data)
  (provide/contract [f (((non-empty-listof posn/c) . -> . (listof posn/c)) . -> . any/c)]))

(require 'cut-tail 'H)
(f cut-tail)