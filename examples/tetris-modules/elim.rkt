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


(module consts racket
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Defined constants
  ;; opaque
  (provide/contract [block-size exact-nonnegative-integer?]
                    [board-width exact-nonnegative-integer?]
                    [board-height exact-nonnegative-integer?]))


(module bset racket
  (require 'data)
  ;; opaque
  (provide/contract [blocks-contains? (bset/c block/c . -> . boolean?)]
                    [blocks=? (bset/c bset/c . -> . boolean?)]
                    [blocks-subset? (bset/c bset/c . -> . boolean?)]
                    [blocks-intersect (bset/c bset/c . -> . bset/c)]
                    [blocks-count (bset/c . -> . exact-nonnegative-integer?)]
                    [blocks-overflow? (bset/c . -> . boolean?)]
                    [blocks-move (exact-nonnegative-integer? exact-nonnegative-integer? bset/c . -> . bset/c)]
                    [blocks-rotate-cw (posn/c bset/c . -> . bset/c)]
                    [blocks-rotate-ccw (posn/c bset/c . -> . bset/c)]
                    [blocks-change-color (bset/c color/c . -> . bset/c)]
                    [blocks-row (bset/c exact-nonnegative-integer? . -> . bset/c)]
                    [full-row? (bset/c exact-nonnegative-integer? . -> . boolean?)])
)


(module elim-row racket
  (require 'data 'bset 'consts 'elim-row)
  (provide/contract [elim-row (bset/c exact-nonnegative-integer? exact-nonnegative-integer? . -> . bset/c)])
)

(module elim racket
  (require 'data 'bset 'consts 'elim-row)

  ;; eliminate-full-rows : BSet -> BSet
  ;; Eliminate all full rows and shift down appropriately.
  (define (eliminate-full-rows bs)
    (elim-row bs board-height 0))
  (provide/contract [eliminate-full-rows (bset/c . -> . bset/c)])
)

(module H racket
  (require 'data)
  (provide/contract [b bset/c]))

(require 'elim 'H)
(eliminate-full-rows b)
