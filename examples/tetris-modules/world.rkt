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
                    [full-row? (bset/c exact-nonnegative-integer? . -> . boolean?)]
                    [blocks-union (bset/c bset/c . -> . bset/c)]
                    [blocks-max-x (bset/c . -> . exact-nonnegative-integer?)]
                    [blocks-min-x (bset/c . -> . exact-nonnegative-integer?)]
                    [blocks-max-y (bset/c . -> . exact-nonnegative-integer?)])
)

(module tetras racket
  (require 'bset 'data 'consts 'block)

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

(module aux racket
(require 'data)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Aux

;; list-pick-random : [Listof a] -> a
;; Randomly pick an element from the list.

#;
(define (list-pick-random ls)
  (list-ref ls (random (length ls))))

(provide/contract [list-pick-random ((listof tetra/c) . -> . tetra/c)]
		  [neg-1 exact-nonnegative-integer?] ;; ha!
		  [tetras (listof tetra/c)])
)


(module elim racket
  (require 'data)
  (provide/contract [eliminate-full-rows (bset/c . -> . bset/c)])
)

(module world racket
  (require 'data 'bset 'block 'tetras 'aux 'elim 'consts)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Worlds

;; touchdown : World -> World
;; Add the current tetra's blocks onto the world's block list,
;; and create a new tetra.
(define (touchdown w)
  (world (list-pick-random tetras)
	 (eliminate-full-rows (blocks-union (tetra-blocks (world-tetra w))
					    (world-blocks w)))))

;; world-jump-down : World -> World
;; Take the current tetra and move it down until it lands.
(define (world-jump-down w)
  (cond [(landed? w) w]
        [else (world-jump-down (world (tetra-move 0 1 (world-tetra w))
                                           (world-blocks w)))]))

;; landed-on-blocks? : World -> Boolean
;; Has the current tetra landed on blocks?
;; I.e., if we move the tetra down 1, will it touch any existing blocks?
(define (landed-on-blocks? w)
  (tetra-overlaps-blocks? (tetra-move 0 1 (world-tetra w))
                          (world-blocks w)))

;; landed-on-floor? : World -> Boolean
;; Has the current tetra landed on the floor?
(define (landed-on-floor? w)
  (= (blocks-max-y (tetra-blocks (world-tetra w)))
     (sub1 board-height)))

;; landed? : World -> Boolean
;; Has the current tetra landed?
(define (landed? w)
  (or (landed-on-blocks? w)
      (landed-on-floor? w)))

;; next-world : World -> World
;; Step the world, either touchdown or move the tetra down on step.
(define (next-world w)
  (cond [(landed? w) (touchdown w)]
        [else (world (tetra-move 0 1 (world-tetra w))
			  (world-blocks w))]))
   
;; try-new-tetra : World Tetra -> World
;; Make a world with the new tetra *IF* if doesn't lie on top of some other
;; block or lie off the board. Otherwise, no change.
(define (try-new-tetra w new-tetra)
  (cond [(or (<  (blocks-min-x (tetra-blocks new-tetra)) 0)
	     (>= (blocks-max-x (tetra-blocks new-tetra)) board-width)
	     (tetra-overlaps-blocks? new-tetra (world-blocks w)))
	 w]
	[else (world new-tetra (world-blocks w))]))

;; world-move : Number Number World -> World
;; Move the Tetra by the given X & Y displacement, but only if you can.
;; Otherwise stay put.
(define (world-move dx dy w)
  (try-new-tetra w (tetra-move dx dy (world-tetra w))))

;; world-rotate-ccw : World -> World
;; Rotate the Tetra 90 degrees counterclockwise, but only if you can.
;; Otherwise stay put.
(define (world-rotate-ccw w)
  (try-new-tetra w (tetra-rotate-ccw (world-tetra w))))

;; world-rotate-cw : World -> World
;; Rotate the Tetra 90 degrees clockwise, but only if you can.
;; Otherwise stay put.
(define (world-rotate-cw w)
  (try-new-tetra w (tetra-rotate-cw (world-tetra w))))

;; ghost-blocks : World -> BSet
;; Gray blocks representing where the current tetra would land.
(define (ghost-blocks w)
  (tetra-blocks (tetra-change-color (world-tetra (world-jump-down w))
                                    'gray)))

;; world-key-move : World KeyEvent -> World
;; Move the world according to the given key event.
(define (world-key-move w k)
  (cond [(string=? k "left")
	 (world-move neg-1 0 w)]
	[(string=? k "right")
	 (world-move 1 0 w)]
        [(string=? k "down")
         (world-jump-down w)]
	[(string=? k "a")
	 (world-rotate-ccw w)]
	[(string=? k "s")
	 (world-rotate-cw w)]
	[else w]))

(provide/contract [world-key-move (world/c string? . -> . world/c)]
		  [next-world (world/c . -> . world/c)])
)

(module H racket
	(require 'data)
	(provide/contract [f-world-key-move ((world/c string? . -> . world/c) . -> . any/c)]
			  [f-next-world ((world/c . -> . world/c) . -> . any/c)])
)

(require 'world 'H)

(begin
  (f-world-key-move world-key-move)
  (f-next-world next-world))