#lang var rho

(define-contract block/c
  (struct/c block exact-nonnegative-integer? exact-nonnegative-integer? color/c))
(define-contract posn/c (struct/c posn exact-nonnegative-integer? exact-nonnegative-integer?))
(define-contract color/c symbol?)
(define-contract bset/c (listof block/c))
(define-contract tetra/c (struct/c tetra posn/c bset/c))
(define-contract world/c (struct/c world tetra/c bset/c))

(module data racket
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Data Definitions
  (struct posn (x y))

  ;; A Block is a (block Number Number Color)
  (struct block (x y color))

  ;; A Tetra is a (make-tetra Posn BSet)
  ;; The center point is the point around which the tetra rotates
  ;; when it is rotated.
  (struct tetra (center blocks))

  ;; A Set of Blocks (BSet) is one of:
  ;; - empty
  ;; - (cons Block BSet)
  ;; Order does not matter.  Repetitions are NOT allowed.

  ;; A World is a (make-world Tetra BSet)
  (struct world (tetra blocks))

  ;; posn=? : Posn Posn -> Boolean
  ;; Are the posns the same?
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2))))

  (provide/contract [block (exact-nonnegative-integer? exact-nonnegative-integer? color/c . -> . block/c)]
                    [block? (any/c . -> . boolean?)]
                    [posn (exact-nonnegative-integer? exact-nonnegative-integer? . -> . posn/c)]
                    [posn? (any/c . -> . boolean?)]
                    [posn-x (posn/c . -> . exact-nonnegative-integer?)]
                    [posn-y (posn/c . -> . exact-nonnegative-integer?)]
                    [posn=? (posn/c posn/c . -> . boolean?)]
                    [tetra? (any/c . -> . boolean?)]
                    [world? (any/c . -> . boolean?)]
                    [block-x (block/c . -> . exact-nonnegative-integer?)]
                    [block-y (block/c . -> . exact-nonnegative-integer?)]
                    [block-color (block/c . -> . color/c)]
                    [tetra (posn/c bset/c . -> . tetra/c)]
                    [tetra-center (tetra/c . -> . posn/c)]
                    [tetra-blocks (tetra/c . -> . bset/c)]
                    [world (tetra/c bset/c . -> . world/c)]
                    [world-tetra (world/c . -> . tetra/c)]
                    [world-blocks (world/c . -> . bset/c)]))


(module block racket
  (require 'data)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Blocks

  ;; block=? : Block Block -> Boolean
  ;; Determines if two blocks are the same (ignoring color).
  (define (block=? b1 b2)
    (and (= (block-x b1) (block-x b2))
         (= (block-y b1) (block-y b2))))

  ;; block-move : Number Number Block -> Block
  (define (block-move dx dy b)
    (block (+ dx (block-x b))
           (+ dy (block-y b))
           (block-color b)))

  ;; block-rotate-ccw : Posn Block -> Block
  ;; Rotate the block 90 counterclockwise around the posn.
  (define (block-rotate-ccw c b)
    (block (+ (posn-x c)
              (- (posn-y c)
                 (block-y b)))
           (+ (posn-y c)
              (- (block-x b)
                 (posn-x c)))
           (block-color b)))

  ;; block-rotate-cw : Posn Block -> Block
  ;; Rotate the block 90 clockwise around the posn.
  (define (block-rotate-cw c b)
    (block-rotate-ccw c (block-rotate-ccw c (block-rotate-ccw c b))))

  (provide/contract [block-rotate-ccw (posn/c block/c . -> . block/c)]
                    [block-rotate-cw (posn/c block/c . -> . block/c)]
                    [block=? (block/c block/c . -> . boolean?)]
                    [block-move (exact-nonnegative-integer? exact-nonnegative-integer? block/c . -> . block/c)])
)



  (module H racket
    (require 'data)
    (provide/contract
     [f-rotate ((posn/c block/c . -> . block/c) . -> . any/c)]
     [f-move ((exact-nonnegative-integer? exact-nonnegative-integer? block/c . -> . block/c) . -> . any/c)]
     [f-= ((block/c block/c . -> . boolean?) . -> . any/c)]))

(require 'block 'H)

(begin
 (f-rotate block-rotate-cw)
 (f-rotate block-rotate-ccw)
 (f-= block=?)
 (f-move block-move))