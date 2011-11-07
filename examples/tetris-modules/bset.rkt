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

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Defined constants

  (define block-size   20)  ;; in Pixels
  (define board-width  2)  ;; in Blocks
  (define board-height 20)

  (provide/contract [block (exact-nonnegative-integer? exact-nonnegative-integer? color/c . -> . block/c)]
                    [block? (any/c . -> . boolean?)]
                    [block-size exact-nonnegative-integer?]
                    [board-height exact-nonnegative-integer?]
                    [board-width exact-nonnegative-integer?]
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

  ;; opaque
  #|

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
  |#
  (provide/contract [block-rotate-ccw (posn/c block/c . -> . block/c)]
                    [block-rotate-cw (posn/c block/c . -> . block/c)]
                    [block=? (block/c block/c . -> . boolean?)]
                    [block-move (exact-nonnegative-integer? exact-nonnegative-integer? block/c . -> . block/c)])
)

(module list-fun racket
  (require 'data)
  (provide/contract
   [max (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?)]
   [min (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?)]
   [ormap ((block/c . -> . boolean?) (listof any/c) . -> . boolean?)]
   [andmap ((block/c . -> . boolean?) (listof any/c) . -> . boolean?)]
   [map ((block/c . -> . block/c) bset/c . -> . bset/c)]
   [filter ((block/c . -> . boolean?) bset/c . -> . bset/c)]
   [length ((listof any/c) . -> . exact-nonnegative-integer?)]
   [foldr ((block/c bset/c . -> . bset/c) bset/c bset/c . -> . bset/c)]
   [foldr-n ((block/c exact-nonnegative-integer? . -> . exact-nonnegative-integer?) exact-nonnegative-integer? bset/c . -> . exact-nonnegative-integer?)]))


(module bset racket
  (require 'data 'block 'list-fun)
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Sets of blocks

  ;; blocks-contains? : BSet Block -> Boolean
  ;; Determine if the block is in the set of blocks.
  (define (blocks-contains? bs b)
    (ormap (λ (c) (block=? b c)) bs))

  ;; blocks-subset? : BSet BSet -> Boolean
  ;; is every element in bs1 also in bs2?
  (define (blocks-subset? bs1 bs2)
    (andmap (λ (b) (blocks-contains? bs2 b)) bs1))

  ;; blocks=? : BSet BSet -> Boolean
  ;; Determine if given sets of blocks are equal.
  (define (blocks=? bs1 bs2)
    (and (blocks-subset? bs1 bs2)
         (blocks-subset? bs2 bs1)))

  ;; blocks-intersect : BSet BSet -> BSet
  ;; Return the set of blocks that appear in both sets.
  (define (blocks-intersect bs1 bs2)
    (filter (λ (b) (blocks-contains? bs2 b)) bs1))

  ;; blocks-count : BSet -> Nat
  ;; Return the number of blocks in the set.
  (define (blocks-count bs)
    (length bs))  ;; No duplicates, cardinality = length.

  ;; blocks-move : Number Number BSet -> BSet
  ;; Move each block by the given X & Y displacement.
  (define (blocks-move dx dy bs)
    (map (λ (b) (block-move dx dy b)) bs))

  ;; blocks-rotate-ccw : Posn BSet -> BSet
  ;; Rotate the blocks 90 counterclockwise around the posn.
  (define (blocks-rotate-ccw c bs)
    (map (λ (b) (block-rotate-ccw c b)) bs))

  ;; blocks-rotate-cw : Posn BSet -> BSet
  ;; Rotate the blocks 90 clockwise around the posn.
  (define (blocks-rotate-cw c bs)
    (map (λ (b) (block-rotate-cw c b)) bs))

  ;; blocks-change-color : BSet Color -> BSet
  (define (blocks-change-color bs c)
    (map (λ (b) (block (block-x b)
                       (block-y b)
                       c))
         bs))

  ;; blocks-row : BSet Number -> BSet
  ;; Return the set of blocks in the given row.
  (define (blocks-row bs i)
    (filter (λ (b) (= i (block-y b))) bs))

  ;; full-row? : BSet Nat -> Boolean
  ;; Are there a full row of blocks at the given row in the set.
  (define (full-row? bs i)
    (= board-width (blocks-count (blocks-row bs i))))

  ;; blocks-overflow? : BSet -> Boolean
  ;; Have any of the blocks reach over the top of the board?
  (define (blocks-overflow? bs)
    (ormap (λ (b) (<= (block-y b) 0)) bs))

  ;; blocks-union : BSet BSet -> BSet
  ;; Union the two sets of blocks.
  (define (blocks-union bs1 bs2)
    (foldr (λ (b bs)
             (cond [(blocks-contains? bs b) bs]
                   [else (cons b bs)]))
           bs2
           bs1))

  ;; blocks-max-y : BSet -> Number
  ;; Compute the maximum y coordinate;
  ;; if set is empty, return 0, the coord of the board's top edge.
  (define (blocks-max-y bs)
    (foldr-n (λ (b n) (max (block-y b) n)) 0 bs))

  ;; blocks-min-x : BSet -> Number
  ;; Compute the minimum x coordinate;
  ;; if set is empty, return the coord of the board's right edge.
  (define (blocks-min-x bs)
    (foldr-n (λ (b n) (min (block-x b) n)) board-width bs))

  ;; blocks-max-x : BSet -> Number
  ;; Compute the maximum x coordinate;
  ;; if set is empty, return 0, the coord of the board's left edge.
  (define (blocks-max-x bs)
    (foldr-n (λ (b n) (max (block-x b) n)) 0 bs))

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
                    [full-row? (bset/c exact-nonnegative-integer? . -> . boolean?)]
                    [blocks-union (bset/c bset/c . -> . bset/c)]
                    [blocks-max-x (bset/c . -> . exact-nonnegative-integer?)]
                    [blocks-min-x (bset/c . -> . exact-nonnegative-integer?)]
                    [blocks-max-y (bset/c . -> . exact-nonnegative-integer?)]

)
)

(module H racket
  (require 'data)
  (provide/contract
   [f0 ((bset/c block/c . -> . boolean?) . -> . any/c)]
   [f1 ((bset/c bset/c . -> . boolean?) . -> . any/c)]
   [f2 ((bset/c . -> . exact-nonnegative-integer?) . -> . any/c)]
   [f3 ((bset/c bset/c . -> . bset/c) . -> . any/c)]
   [f4 ((bset/c . -> . boolean?) . -> . any/c)]
   [f-blocks-move ((exact-nonnegative-integer? exact-nonnegative-integer? bset/c . -> . bset/c) . -> . any/c)]
   [f-rotate ((posn/c bset/c . -> . bset/c) . -> . any/c)]
   [f-blocks-change-color ((bset/c color/c . -> . bset/c) . -> . any/c)]
   [f-blocks-row ((bset/c exact-nonnegative-integer? . -> . bset/c) . -> . any/c)]
   [f-full-row? ((bset/c exact-nonnegative-integer? . -> . boolean?) . -> . any/c)]
   [f-blocks-union ((bset/c bset/c . -> . bset/c) . -> . any/c)]
))


(require 'H 'bset)

(begin
  ;(f0 blocks-contains?)
  ;(f1 blocks-subset?)
  ;(f1 blocks=?)
  #; (f2 blocks-count)
  ;(f3 blocks-intersect)
  ;(f4 blocks-overflow?)
  ;(f-blocks-move blocks-move)
  ;(f-rotate blocks-rotate-ccw)
  ;(f-rotate blocks-rotate-cw)
  ;(f-blocks-change-color blocks-change-color)
  ;(f-blocks-change-color blocks-change-color)
  ;(f-full-row? full-row?)
  ;(f-blocks-row blocks-row)
  ;(f-blocks-union blocks-union)
  (f2 blocks-max-x)
  (f2 blocks-max-y)
  (f2 blocks-min-x)
  )