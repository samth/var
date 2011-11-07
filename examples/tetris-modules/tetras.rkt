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

  ;; A Tetra is a (tetra Posn BSet)
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

  (define (not x) (if x #f #t))

  (provide/contract [block (exact-nonnegative-integer? exact-nonnegative-integer? color/c . -> . block/c)]
                    [block? (any/c . -> . boolean?)]
		    [not (boolean? . -> . boolean?)]
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

(module tetras racket
  (require 'bset 'data 'consts 'block)
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Tetras
  
  ;; tetra-move : Number Number Tetra -> Tetra
  ;; Move the Tetra by the given X & Y displacement.
  (define (tetra-move dx dy t)
    (tetra (posn (+ dx (posn-x (tetra-center t)))
		 (+ dy (posn-y (tetra-center t))))
	   (blocks-move dx dy (tetra-blocks t))))

  ;; tetra-rotate-ccw : Tetra -> Tetra
  ;; Rotate the tetra 90 degrees counterclockwise around its center.
  (define (tetra-rotate-ccw t)
    (tetra (tetra-center t)
	   (blocks-rotate-ccw (tetra-center t)
			      (tetra-blocks t))))

  ;; tetra-rotate-cw : Tetra -> Tetra
  ;; Rotate the tetra 90 degrees clockwise around its center.
  (define (tetra-rotate-cw t)
    (tetra (tetra-center t)
	   (blocks-rotate-cw (tetra-center t)
			     (tetra-blocks t))))

  ;; tetra-overlaps-blocks? : Tetra BSet -> Boolean
  ;; Is the tetra on any of the blocks?
  (define (tetra-overlaps-blocks? t bs)
    (not (empty? (blocks-intersect (tetra-blocks t) bs))))

  ;; tetra-change-color : Tetra Color -> Tetra
  ;; Change the color of the given tetra.
  (define (tetra-change-color t c)
    (tetra (tetra-center t)
	   (blocks-change-color (tetra-blocks t) c)))

  (define (build-tetra-blocks color xc yc x1 y1 x2 y2 x3 y3 x4 y4)
    (tetra-move 3 0 
		(tetra (posn xc yc)
		       (list (block x1 y1 color)
			     (block x2 y2 color)
			     (block x3 y3 color)
			     (block x4 y4 color)))))

  ;; Bogus centers
  #;(define tetras
    (list 
     (build-tetra-blocks 'green  	1/2 -3/2    0 -1 0 -2 1 -1 1 -2)
     (build-tetra-blocks 'blue   	1   -1      0 -1 1 -1 2 -1 3 -1)
     (build-tetra-blocks 'purple 	1   -1      0 -1 1 -1 2 -1 2 -2)
     (build-tetra-blocks 'cyan   	1   -1      0 -1 1 -1 2 -1 0 -2)
     (build-tetra-blocks 'orange  1   -1      0 -1 1 -1 2 -1 1 -2)
     (build-tetra-blocks 'red     1   -1      0 -1 1 -1 1 -2 2 -2)
     (build-tetra-blocks 'pink    1   -1      0 -2 1 -2 1 -1 2 -1)
     ))
 
  (provide/contract ;[tetras (listof tetra/c)]
		    [tetra-move (exact-nonnegative-integer? exact-nonnegative-integer? tetra/c . -> . tetra/c)]
		    [tetra-rotate-ccw (tetra/c . -> . tetra/c)]
		    [tetra-rotate-cw (tetra/c . -> . tetra/c)]
		    [tetra-overlaps-blocks? (tetra/c bset/c . -> . boolean?)]
		    [build-tetra-blocks (color/c exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 . -> . 
						 tetra/c)]
		    [tetra-change-color (tetra/c color/c . -> . tetra/c)])
 )

(module H racket
  (require 'data)
  (provide/contract [n exact-nonnegative-integer?]
		    [t tetra/c]
		    [f-tetra-move ((exact-nonnegative-integer? exact-nonnegative-integer? tetra/c . -> . tetra/c) . -> . any/c)]
		    [f-tetra-rotate-ccw ((tetra/c . -> . tetra/c) . -> . any/c)]
		    [f-tetra-rotate-cw ((tetra/c . -> . tetra/c) . -> . any/c)]
		    [f-tetra-overlaps-blocks? ((tetra/c bset/c . -> . boolean?) . -> . any/c)]
		    [f-build-tetra-blocks ((color/c exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 exact-nonnegative-integer?
						 . -> . 
						 tetra/c) . -> . any/c)]
		    [f-tetra-change-color ((tetra/c color/c . -> . tetra/c) . -> . any/c)]))

(require 'H 'tetras)

(begin
  #;(f-tetra-move tetra-move)
  #;(f-tetra-change-color tetra-change-color)
  #;(f-tetra-rotate-cw tetra-rotate-cw)
#;#;  (f-tetra-rotate-ccw tetra-rotate-ccw)
  (f-tetra-overlaps-blocks? tetra-overlaps-blocks?)

  (f-build-tetra-blocks build-tetra-blocks))

