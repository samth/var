#lang var rho

(define-contract block/c
  (struct/c block exact-nonnegative-integer? exact-nonnegative-integer? color/c))
(define-contract posn/c (struct/c posn exact-nonnegative-integer? exact-nonnegative-integer?))
(define-contract color/c symbol?)
(define-contract bset/c (listof block/c))
(define-contract tetra/c (struct/c tetra posn/c bset/c))
(define-contract world/c (struct/c world tetra/c bset/c))


(module image racket
  ;(require 2htdp/image) ;; COMMENT OUT THIS LINE
  (provide/contract
   [/ (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?)]
   [image? (any/c . -> . boolean?)]
   [overlay (image? image? . -> . image?)]
   [rectangle (exact-nonnegative-integer? exact-nonnegative-integer? color/c color/c . -> . image?)]
   [circle (exact-nonnegative-integer? string? string? . -> . image?)]
   [empty-scene (exact-nonnegative-integer? exact-nonnegative-integer? . -> . image?)]
   [place-image (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]))

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
	(require 'data)
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Defined constants
  ;; opaque
  (provide/contract [block-size exact-nonnegative-integer?]
                    [board-width exact-nonnegative-integer?]
                    [board-height exact-nonnegative-integer?]))


(module list-fun racket
  (require 'data 'image)
  (provide/contract
   [max (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?)]
   [min (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?)]
   [ormap ((block/c . -> . boolean?) (listof any/c) . -> . boolean?)]
   [andmap ((block/c . -> . boolean?) (listof any/c) . -> . boolean?)]
   [map ((block/c . -> . block/c) bset/c . -> . bset/c)]
   [filter ((block/c . -> . boolean?) bset/c . -> . bset/c)]
   [append (bset/c bset/c . -> . bset/c)]
   [length ((listof any/c) . -> . exact-nonnegative-integer?)]
   [foldr ((block/c bset/c . -> . bset/c) bset/c bset/c . -> . bset/c)]
   [foldr-i ((block/c image? . -> . image?) image? bset/c . -> . image?)]
   [foldr-n ((block/c exact-nonnegative-integer? . -> . exact-nonnegative-integer?) exact-nonnegative-integer? bset/c . -> . exact-nonnegative-integer?)]))


(module world racket 
	(require 'data)
	(provide/contract [world-key-move (world/c string? . -> . world/c)]
			  [next-world (world/c . -> . world/c)]
			  [ghost-blocks (world/c . -> . bset/c)])
	)

(module visual racket
	(require 'image 'data 'consts 'world 'list-fun)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Visualization

;; Visualize whirled peas
;; World -> Scene
(define (world->image w)
  (place-image (blocks->image (append (tetra-blocks (world-tetra w))
                                      (append (ghost-blocks w)
                                              (world-blocks w))))
	       0 0 
	       (empty-scene (* board-width block-size)
			    (* board-height block-size))))
  
;; BSet -> Scene
(define (blocks->image bs)
  (foldr-i (λ (b img)
           (cond [(<= 0 (block-y b)) (place-block b img)]
                 [else img]))
         (empty-scene (add1 (* board-width block-size)) 
                      (add1 (* board-height block-size)))
         bs))

;; Visualizes a block.
;; Block -> Image
(define (block->image b)
  (overlay 
    (rectangle (add1 block-size) (add1 block-size) 'solid (block-color b))
    (rectangle (add1 block-size) (add1 block-size) 'outline 'black)))

;; Block Scene -> Scene
(define (place-block b scene)
  (place-image (block->image b)
	       (+ (* (block-x b) block-size) (/ block-size 2))
	       (+ (* (block-y b) block-size) (/ block-size 2))
	       scene))

(define (world0)
  (make-world (list-pick-random tetras) empty))
(provide/contract [world->image (world/c . -> . image?)]
		  [blocks->image (bset/c . -> . image?)]
		  [block->image (block/c . -> . image?)]
		  [place-block (block/c image? . -> . image?)])
)

(module H racket
	(require 'data 'image)
	(provide/contract [f-world->image ((world/c . -> . image?) . -> . any/c)]
			  [bs bset/c]
			  [b block/c]
			  [w world/c])
)

(require 'H 'visual 'image)

(f-world->image world->image)
;(world->image w)