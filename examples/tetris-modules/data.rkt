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

  ;; A Block is a (make-block Number Number Color)
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
                    

(module H racket
  (require 'data)
  (provide/contract
   [f-block ((exact-nonnegative-integer? exact-nonnegative-integer? color/c . -> . block/c) . -> . any/c)]
   [f-block? ((any/c . -> . boolean?) . -> . any/c)]
   [f-tetra? ((any/c . -> . boolean?) . -> . any/c)]
   [f-world? ((any/c . -> . boolean?) . -> . any/c)]
   [f-block-x ((block/c . -> . exact-nonnegative-integer?) . -> . any/c)]
   [f-block-y ((block/c . -> . exact-nonnegative-integer?) . -> . any/c)]
   [f-block-color ((block/c . -> . color/c) . -> . any/c)]
   [f-tetra ((posn/c bset/c . -> . tetra/c) . -> . any/c)]
   [f-tetra-center ((tetra/c . -> . posn/c) . -> . any/c)]
   [f-tetra-blocks ((tetra/c . -> . bset/c) . -> . any/c)]
   [f-world ((tetra/c bset/c . -> . world/c) . -> . any/c)]
   [f-world-tetra ((world/c . -> . tetra/c) . -> . any/c)]
   [f-world-blocks ((world/c . -> . bset/c) . -> . any/c)]))

(require 'data 'H)

(begin
 (f-world-blocks world-blocks)
 (f-world-tetra world-tetra)
 (f-world world)
 (f-world? world?)
 (f-tetra tetra)
 (f-tetra-center tetra-center)
 (f-tetra-blocks tetra-blocks)
 (f-tetra? tetra?)
 (f-block block)
 (f-block? block?)
 (f-block-color block-color)
 (f-block-x block-x)
 (f-block-y block-y))