#lang scheme
;;   _/_/_/_/_/           _/                _/           
;;      _/      _/_/   _/_/_/_/  _/  _/_/        _/_/_/  
;;     _/    _/_/_/_/   _/      _/_/      _/  _/_/       
;;    _/    _/         _/      _/        _/      _/_/    
;;   _/      _/_/_/     _/_/  _/        _/  _/_/_/

;; Copyright (c) 2007, 2008, 2010 David Van Horn
;; Licensed under the Academic Free License version 3.0

;; (at dvanhorn (dot ccs neu edu))

;; This program has only partial test coverage.

(require 2htdp/universe)
(require test-engine/scheme-tests)
(require lang/posn)
(require (except-in htdp/image image? image=?))
(provide (all-defined-out))
         
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Defined constants

(define block-size   20)  ;; in Pixels
(define board-width  10)  ;; in Blocks
(define board-height 20)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Data Definitions

;; A Block is a (make-block Number Number Color)
(define-struct block (x y color))

;; A Tetra is a (make-tetra Posn BSet)
;; The center point is the point around which the tetra rotates
;; when it is rotated.
(define-struct tetra (center blocks))

;; A Set of Blocks (BSet) is one of:
;; - empty
;; - (cons Block BSet)
;; Order does not matter.  Repetitions are NOT allowed.

;; A World is a (make-world Tetra BSet)
(define-struct world (tetra blocks))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Blocks

;; block=? : Block Block -> Boolean
;; Determines if two blocks are the same (ignoring color).
(define (block=? b1 b2)
  (and (= (block-x b1) (block-x b2))
       (= (block-y b1) (block-y b2))))

"Identical blocks are equal."
(check-expect (block=? (make-block 0 0 'black)
                       (make-block 0 0 'black))
              true)
   
"Identical (modulo color) blocks are equal."
(check-expect (block=? (make-block 0 0 'black)
                       (make-block 0 0 'red))
              true)

"Blocks with different coordinates are different."
(check-expect (block=? (make-block 0 1 'black)
                       (make-block 0 0 'black))
              false)
(check-expect (block=? (make-block 0 0 'black)
                       (make-block 0 1 'black))
              false)

;; block-move : Number Number Block -> Block
(define (block-move dx dy b)
  (make-block (+ dx (block-x b))
              (+ dy (block-y b))
              (block-color b)))

"Block move."
(check-expect (block=? (block-move 0 0 (make-block 0 0 'black))
                       (make-block 0 0 'black))
              true)
(check-expect (block=? (block-move 0 1 (make-block 0 0 'black))
                       (make-block 0 1 'black))
              true)

;; block-rotate-ccw : Posn Block -> Block
;; Rotate the block 90 counterclockwise around the posn.
(define (block-rotate-ccw c b)
  (make-block (+ (posn-x c)
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sets of blocks

;; blocks-contains? : BSet Block -> Boolean
;; Determine if the block is in the set of blocks.
(define (blocks-contains? bs b)
  (ormap (lambda (c) (block=? b c)) bs))

"Block set membership."
(check-expect (blocks-contains? empty (make-block 0 0 'black))
              false)
(check-expect (blocks-contains? (list (make-block 0 0 'black))
                                (make-block 0 0 'black))
              true)
(check-expect (blocks-contains? (list (make-block 0 1 'black))
                                (make-block 0 0 'black))
              false)

;; blocks-subset? : BSet BSet -> Boolean
;; is every element in bs1 also in bs2?
(define (blocks-subset? bs1 bs2)
  (andmap (lambda (b) (blocks-contains? bs2 b)) bs1))

"Block set containment."
(check-expect (blocks-subset? empty empty)
              true)
(check-expect (blocks-subset? empty (list (make-block 0 0 'black)))
              true)
(check-expect (blocks-subset? (list (make-block 0 0 'black))
                              (list (make-block 0 0 'black)))
              true)

;; blocks=? : BSet BSet -> Boolean
;; Determine if given sets of blocks are equal.
(define (blocks=? bs1 bs2)
   (and (blocks-subset? bs1 bs2) 
        (blocks-subset? bs2 bs1)))

"Block set equality."
(check-expect (blocks=? (list (make-block 0 0 'black))
                        (list (make-block 0 0 'black)))
              true)
(check-expect (blocks=? (list (make-block 0 0 'black))
                        (list (make-block 0 1 'black)))
              false)

;; blocks-intersect : BSet BSet -> BSet
;; Return the set of blocks that appear in both sets.
(define (blocks-intersect bs1 bs2)
  (filter (lambda (b) (blocks-contains? bs2 b)) bs1))

"Block set intersection."
(check-expect (blocks=? (blocks-intersect empty empty) 
                        empty)
              true)
(check-expect (blocks=? (blocks-intersect empty (list (make-block 0 0 'black)))
                        empty)
              true)
(check-expect (blocks=? (blocks-intersect (list (make-block 0 0 'black)) empty) 
                        empty)
              true)
(check-expect (blocks=? (blocks-intersect (list (make-block 0 0 'black))
                                          (list (make-block 0 0 'black)))
                        (list (make-block 0 0 'black)))
              true)

;; blocks-union : BSet BSet -> BSet
;; Union the two sets of blocks.
(define (blocks-union bs1 bs2)
  (foldr (lambda (b bs)
           (cond [(blocks-contains? bs b) bs]
                 [else (cons b bs)]))
         bs2
         bs1))

"Block set union."
(check-expect (blocks=? (blocks-union empty empty) empty)
              true)
(check-expect (blocks=? (blocks-union empty (list (make-block 0 0 'black)))
                        (list (make-block 0 0 'black)))
              true)
(check-expect (blocks=? (blocks-union (list (make-block 0 0 'black)) empty) 
                        (list (make-block 0 0 'black)))
              true)
(check-expect (blocks=? (blocks-union (list (make-block 0 0 'black))
                                      (list (make-block 0 0 'black)))
                        (list (make-block 0 0 'black)))
              true)
(check-expect (blocks=? (blocks-union (list (make-block 0 0 'black))
                                      (list (make-block 0 1 'black)))
                        (list (make-block 0 0 'black)
                              (make-block 0 1 'black)))
              true)

;; blocks-count : BSet -> Nat
;; Return the number of blocks in the set.
(define (blocks-count bs)
  (length bs))  ;; No duplicates, cardinality = length.

"Block set cardinality."
(check-expect (blocks-count empty) 0)
(check-expect (blocks-count (list (make-block 0 0 'black))) 1)
(check-expect (blocks-count (blocks-union (list (make-block 0 0 'black))
                                          (list (make-block 0 0 'black))))
              1)
(check-expect (blocks-count (blocks-union (list (make-block 0 0 'black))
                                          (list (make-block 1 1 'black))))
              2)

;; blocks-max-y : BSet -> Number
;; Compute the maximum y coordinate;
;; if set is empty, return 0, the coord of the board's top edge.
(define (blocks-max-y bs)
  (foldr (lambda (b n) (max (block-y b) n)) 0 bs))

"Block set maximal y-coordinate."
(check-expect (blocks-max-y empty) 0)
(check-expect (blocks-max-y (list (make-block 0 1 'black))) 1)
(check-expect (blocks-max-y (list (make-block 1 0 'black))) 0)

;; blocks-min-x : BSet -> Number
;; Compute the minimum x coordinate;
;; if set is empty, return the coord of the board's right edge.
(define (blocks-min-x bs)
  (foldr (lambda (b n) (min (block-x b) n)) board-width bs))

"Block set minimal x-coordinate."
(check-expect (blocks-min-x empty) board-width)
(check-expect (blocks-min-x (list (make-block 0 1 'black))) 0)
(check-expect (blocks-min-x (list (make-block 1 0 'black))) 1)

;; blocks-max-x : BSet -> Number
;; Compute the maximum x coordinate;
;; if set is empty, return 0, the coord of the board's left edge.
(define (blocks-max-x bs)
  (foldr (lambda (b n) (max (block-x b) n)) 0 bs))

"Block set maximal x-coordinate."
(check-expect (blocks-max-x empty) 0)
(check-expect (blocks-max-x (list (make-block 0 1 'black))) 0)
(check-expect (blocks-max-x (list (make-block 1 0 'black))) 1)

;; blocks-move : Number Number BSet -> BSet
;; Move each block by the given X & Y displacement.
(define (blocks-move dx dy bs)
  (map (lambda (b) (block-move dx dy b)) bs))

"Block set move."
(check-expect (blocks=? (blocks-move 0 0 empty) empty)
              true)
(check-expect (blocks=? (blocks-move 0 0 (list (make-block 0 0 'black)))
                        (list (make-block 0 0 'black)))
              true)
(check-expect (blocks=? (blocks-move 1 1 (list (make-block 0 0 'black)))
                        (list (make-block 1 1 'black)))
              true)

;; blocks-rotate-ccw : Posn BSet -> BSet
;; Rotate the blocks 90 counterclockwise around the posn.
(define (blocks-rotate-ccw c bs)
  (map (lambda (b) (block-rotate-ccw c b)) bs))

;; blocks-rotate-cw : Posn BSet -> BSet
;; Rotate the blocks 90 clockwise around the posn.
(define (blocks-rotate-cw c bs)
  (map (lambda (b) (block-rotate-cw c b)) bs))

;; blocks-change-color : BSet Color -> BSet
(define (blocks-change-color bs c)
  (map (lambda (b) (make-block (block-x b)
                               (block-y b)
                               c))
       bs))

;; blocks-overflow? : BSet -> Boolean
;; Have any of the blocks reach over the top of the board?
(define (blocks-overflow? bs)
  (ormap (lambda (b) (<= (block-y b) 0)) bs))

"Block overflow."
(check-expect (blocks-overflow? empty) 
              false)
(check-expect (blocks-overflow? (list (make-block 0 0 'black))) 
              true)
(check-expect (blocks-overflow? (list (make-block 0 1 'black))) 
              false)

;; blocks-row : BSet Number -> BSet
;; Return the set of blocks in the given row.
(define (blocks-row bs i)
  (filter (lambda (b) (= i (block-y b))) bs))

"Block set row selection."
(check-expect (blocks=? (blocks-row empty 0) empty) 
              true)
(check-expect (blocks=? (blocks-row (list (make-block 0 0 'black)) 1) empty) 
              true)
(check-expect (blocks=? (blocks-row (list (make-block 0 0 'black)) 0)
                        (list (make-block 0 0 'black)))
              true)
    
;; full-row? : BSet Nat -> Boolean
;; Are there a full row of blocks at the given row in the set.
(define (full-row? bs i)
  (= board-width (blocks-count (blocks-row bs i))))

"Full row."
(check-expect (full-row? empty 0) false)
             
;; eliminate-full-rows : BSet -> BSet
;; Eliminate all full rows and shift down appropriately.
(define (eliminate-full-rows bs)
  (local [(define (elim-row i offset)
            (cond [(< i 0) empty]
                  [(full-row? bs i)   (elim-row (sub1 i) (add1 offset))]
                  [else (blocks-union (elim-row (sub1 i) offset)
                                      (blocks-move 0 offset (blocks-row bs i)))]))]
    (elim-row board-height 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tetras

;; tetra-move : Number Number Tetra -> Tetra
;; Move the Tetra by the given X & Y displacement.
(define (tetra-move dx dy t)
  (make-tetra (make-posn (+ dx (posn-x (tetra-center t)))
			 (+ dy (posn-y (tetra-center t))))
	      (blocks-move dx dy (tetra-blocks t))))

;; tetra-rotate-ccw : Tetra -> Tetra
;; Rotate the tetra 90 degrees counterclockwise around its center.
(define (tetra-rotate-ccw tetra)
  (make-tetra (tetra-center tetra)
	      (blocks-rotate-ccw (tetra-center tetra)
				 (tetra-blocks tetra))))

;; tetra-rotate-cw : Tetra -> Tetra
;; Rotate the tetra 90 degrees clockwise around its center.
(define (tetra-rotate-cw tetra)
  (make-tetra (tetra-center tetra)
	      (blocks-rotate-cw (tetra-center tetra)
				(tetra-blocks tetra))))

;; tetra-overlaps-blocks? : Tetra BSet -> Boolean
;; Is the tetra on any of the blocks?
(define (tetra-overlaps-blocks? t bs)
  (not (empty? (blocks-intersect (tetra-blocks t) bs))))

;; tetra-change-color : Tetra Color -> Tetra
;; Change the color of the given tetra.
(define (tetra-change-color t c)
  (make-tetra (tetra-center t)
              (blocks-change-color (tetra-blocks t) c)))

(define (build-tetra-blocks color xc yc x1 y1 x2 y2 x3 y3 x4 y4)
  (tetra-move 3 0 
              (make-tetra (make-posn xc yc)
                          (list (make-block x1 y1 color)
                                (make-block x2 y2 color)
                                (make-block x3 y3 color)
                                (make-block x4 y4 color)))))

;; Bogus centers
(define tetras
  (list 
   (build-tetra-blocks 'green  	1/2 -3/2    0 -1 0 -2 1 -1 1 -2)
   (build-tetra-blocks 'blue   	1   -1      0 -1 1 -1 2 -1 3 -1)
   (build-tetra-blocks 'purple 	1   -1      0 -1 1 -1 2 -1 2 -2)
   (build-tetra-blocks 'cyan   	1   -1      0 -1 1 -1 2 -1 0 -2)
   (build-tetra-blocks 'orange  1   -1      0 -1 1 -1 2 -1 1 -2)
   (build-tetra-blocks 'red     1   -1      0 -1 1 -1 1 -2 2 -2)
   (build-tetra-blocks 'pink    1   -1      0 -2 1 -2 1 -1 2 -1)
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Worlds

;; touchdown : World -> World
;; Add the current tetra's blocks onto the world's block list,
;; and create a new tetra.
(define (touchdown w)
  (make-world (list-pick-random tetras)
	      (eliminate-full-rows (blocks-union (tetra-blocks (world-tetra w))
                                                 (world-blocks w)))))

;; world-jump-down : World -> World
;; Take the current tetra and move it down until it lands.
(define (world-jump-down w)
  (cond [(landed? w) w]
        [else (world-jump-down (make-world (tetra-move 0 1 (world-tetra w))
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
        [else (make-world (tetra-move 0 1 (world-tetra w))
			  (world-blocks w))]))
   
;; try-new-tetra : World Tetra -> World
;; Make a world with the new tetra *IF* if doesn't lie on top of some other
;; block or lie off the board. Otherwise, no change.
(define (try-new-tetra w new-tetra)
  (cond [(or (<  (blocks-min-x (tetra-blocks new-tetra)) 0)
	     (>= (blocks-max-x (tetra-blocks new-tetra)) board-width)
	     (tetra-overlaps-blocks? new-tetra (world-blocks w)))
	 w]
	[else (make-world new-tetra (world-blocks w))]))

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
  (cond [(key=? k "left")
	 (world-move -1 0 w)]
	[(key=? k "right")
	 (world-move 1 0 w)]
        [(key=? k "down")
         (world-jump-down w)]
	[(key=? k "a")
	 (world-rotate-ccw w)]
	[(key=? k "s")
	 (world-rotate-cw w)]
	[else w]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Aux

;; list-pick-random : [Listof a] -> a
;; Randomly pick an element from the list.
(define (list-pick-random ls)
  (list-ref ls (random (length ls))))


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
  (foldr (lambda (b img)
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

(define world0
  (make-world (list-pick-random tetras) empty))

(test)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Big bang

(big-bang world0 
          (on-tick next-world (/ 1.0 5))
          (stop-when (lambda (w) (blocks-overflow? (world-blocks w))))
          (on-draw world->image)
          (on-key world-key-move))
