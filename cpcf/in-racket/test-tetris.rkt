#lang racket

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")
(require "helper.rkt")

(define c/color `(flat string?))
(define c/block `(cons/c (flat real?) (cons/c (flat real?) ,c/color)))
(define c/posn `(cons/c (flat real?) (flat real?)))
(define c/bset (c/list-of c/block))
(define c/tetra `(cons/c ,c/posn ,c/bset))
(define c/world `(cons/c ,c/tetra ,c/bset))


(define modl-data
  `(module data
     (provide
      [block ((flat real?) (flat real?) ,c/color ↦ ,c/block)]
      [block? (,c/any ↦ (flat bool?))]
      [posn ((flat real?) (flat real?) ↦ ,c/posn)]
      [posn? (,c/any ↦ (flat bool?))]
      [posn-x (,c/posn ↦ (flat real?))]
      [posn-y (,c/posn ↦ (flat real?))]
      [posn=? (,c/posn ,c/posn ↦ (flat bool?))]
      [tetra? (,c/any ↦ (flat bool?))]
      [world? (,c/any ↦ (flat bool?))]
      [block-x (,c/block ↦ (flat real?))]
      [block-y (,c/block ↦ (flat real?))]
      [block-color (,c/block ↦ ,c/color)]
      [tetra (,c/posn ,c/bset ↦ ,c/tetra)]
      [tetra-center (,c/tetra ↦ ,c/posn)]
      [tetra-blocks (,c/tetra ↦ ,c/bset)]
      [world (,c/tetra ,c/bset ↦ ,c/world)]
      [world-tetra (,c/world ↦ ,c/tetra)]
      [world-blocks (,c/world ↦ ,c/bset)])
     
     (define posn cons)
     (define posn-x car)
     (define posn-y cdr)
     (define (posn? x)
       (and (cons? x) (real? (car x)) (real? (cdr x))))
     
     (define (block x y color)
       (cons x (cons y color)))
     (define block-x car)
     (define (block-y b)
       (car (cdr b)))
     (define (block-color b)
       (cdr (cdr b)))
     (define (block? b)
       (and (cons? b) (real? (car b))
            (let ([r (cdr b)])
              (and (cons? r) (real? (car r)) (color? (cdr r))))))
     
     (define tetra cons)
     (define tetra-center car)
     (define tetra-blocks cdr)
     (define (tetra? x)
       (and (cons? x) (posn? (car x)) #|TODO|#))
     
     (define world cons)
     (define world-tetra car)
     (define world-blocks cdr)
     (define (world? x)
       (and (cons? x) (tetra? (car x)) #|TODO|#))
     
     (define (posn=? p1 p2)
       (and (= (posn-x p1) (posn-x p2))
            (= (posn-y p1) (posn-y p2))))
     (define color? string?)))

(define modl-consts
  `(module consts
     (provide
      [block-size (flat nat?)]
      [board-width (flat nat?)]
      [board-height (flat nat?)])
     (define block-size 20)
     (define board-height 20)
     (define board-width 10)))

(define modl-block
  `(module block
     (provide
      [block-rotate-ccw (,c/posn ,c/block ↦ ,c/block)]
      [block-rotate-cw (,c/posn ,c/block ↦ ,c/block)]
      [block=? (,c/block ,c/block ↦ (flat bool?))]
      [block-move ((flat real?) (flat real?) ,c/block ↦ ,c/block)])
     (require data)
     
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
       (block-rotate-ccw c (block-rotate-ccw c (block-rotate-ccw c b))))))

(define modl-block• (opaque modl-block))

(define modl-list-fun
  (opaque
   `(module list-fun
      (provide
       [max ((flat real?) (flat real?) ↦ (flat real?))]
       [min ((flat real?) (flat real?) ↦ (flat real?))]
       [ormap ((,c/block ↦ (flat bool?)) ,(c/list-of c/any) ↦ (flat bool?))]
       [andmap ((,c/block ↦ (flat bool?)) ,(c/list-of c/any) ↦ (flat bool?))]
       [map ((,c/block ↦ ,c/block) ,c/bset ↦ ,c/bset)]
       [filter ((,c/block ↦ (flat bool?)) ,c/bset ↦ ,c/bset)]
       [append (,c/bset ,c/bset ↦ ,c/bset)]
       [length (,(c/list-of c/any) ↦ (flat real?))]
       [foldr ((,c/block ,c/bset ↦ ,c/bset) ,c/bset ,c/bset ↦ ,c/bset)]
       [foldr-i ((,c/block (flat image?) ↦ (flat image?)) (flat image?) ,c/bset ↦ (flat image?))]
       [foldr-n ((,c/block (flat real?) ↦ (flat real?)) (flat real?) ,c/bset ↦ (flat real?))])
      (require image data))))

(define modl-bset
  `(module bset
     (provide
      [blocks-contains? (,c/bset ,c/block ↦ (flat bool?))]
      [blocks=? (,c/bset ,c/bset ↦ (flat bool?))]
      [blocks-subset? (,c/bset ,c/bset ↦ (flat bool?))]
      [blocks-intersect (,c/bset ,c/bset ↦ ,c/bset)]
      [blocks-count (,c/bset ↦ (flat real?))]
      [blocks-overflow? (,c/bset ↦ (flat bool?))]
      [blocks-move ((flat real?) (flat real?) ,c/bset ↦ ,c/bset)]
      [blocks-rotate-cw (,c/posn ,c/bset ↦ ,c/bset)]
      [blocks-rotate-ccw (,c/posn ,c/bset ↦ ,c/bset)]
      [blocks-change-color (,c/bset ,c/color ↦ ,c/bset)]
      [blocks-row (,c/bset (flat real?) ↦ ,c/bset)]
      [full-row? (,c/bset (flat real?) ↦ (flat bool?))]
      [blocks-union (,c/bset ,c/bset ↦ ,c/bset)]
      [blocks-max-x (,c/bset ↦ (flat real?))]
      [blocks-min-x (,c/bset ↦ (flat real?))]
      [blocks-max-y (,c/bset ↦ (flat real?))])
     (require data block list-fun consts)
     
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
       (foldr-n (λ (b n) (max (block-x b) n)) 0 bs))))

(define modl-elim-row
  `(module elim-row
     (provide
      [elim-row (,c/bset (flat nat?) (flat nat?) ↦ ,c/bset)])
     (require data bset consts)
     (define (elim-row bs i offset)
       (cond
         [(< i 0) bs]
         [(full-row? bs i) (elim-row bs (sub1 i) (add1 offset))]
         [else (elim-row (blocks-union bs
                                       (blocks-move 0 offset (blocks-row bs i)))
                         (sub1 i)
                         offset)]))))

(define modl-tetras
  `(module tetras
     (provide ;[tetras (listof ,c/tetra)]
      [tetra-move ((flat nat?) (flat nat?) ,c/tetra ↦ ,c/tetra)]
      [tetra-rotate-ccw (,c/tetra ↦ ,c/tetra)]
      [tetra-rotate-cw (,c/tetra ↦ ,c/tetra)]
      [tetra-overlaps-blocks? (,c/tetra ,c/bset ↦ (flat bool?))]
      [build-tetra-blocks (,c/color (flat nat?)
                                    (flat nat?)
                                    (flat nat?)
                                    (flat nat?)
                                    (flat nat?)
                                    (flat nat?)
                                    (flat nat?)
                                    (flat nat?)
                                    (flat nat?)
                                    (flat nat?)
                                    ↦ 
                                    ,c/tetra)]
      [tetra-change-color (,c/tetra ,c/color ↦ ,c/tetra)])
     (require bset data consts block)
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
          (build-tetra-blocks 'pink    1   -1      0 -2 1 -2 1 -1 2 -1)))))

(define modl-world
  `(module world
     (provide [world-key-move (,c/world (flat string?) ↦ ,c/world)]
              [next-world (,c/world ↦ ,c/world)]
              [ghost-blocks (,c/world ↦ ,c/bset)])
     (require data bset block tetras aux elim consts)
     
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
             [else w]))))

(define modl-image
  (opaque
   `(module image
      (provide
       [image? (,c/any ↦ (flat bool?))]
       [overlay ((flat image?) (flat image?) ↦ (flat image?))]
       [rectangle ((flat nat?) (flat nat?) ,c/color ,c/color ↦ (flat image?))]
       [circle ((flat nat?) (flat string?) (flat string?) ↦ (flat image?))]
       [empty-scene ((flat nat?) (flat nat?) ↦ (flat image?))]
       [place-image ((flat image?) (flat nat?) (flat nat?) (flat image?) ↦ (flat image?))]))))

(define modl-consts• (opaque modl-consts))
(define modl-bset• (opaque modl-bset))
(define modl-elim-row• (opaque modl-elim-row))
(define modl-world• (opaque modl-world))

(define tests
  `(; https://github.com/samth/var/blob/master/examples/tetris-modules/block.rkt
    (,modl-data
     ,modl-block
     ,(opaque
       `(module H
          (provide
           [f-rotate ((,c/posn ,c/block ↦ ,c/block) ↦ ,c/any)]
           [f-move (((flat real?) (flat real?) ,c/block ↦ ,c/block) ↦ ,c/any)]
           [f-= ((,c/block ,c/block ↦ (flat bool?)) ↦ ,c/any)])
          (require data)))
     (require block H)
     (begin
       [f-rotate block-rotate-cw]
       [f-rotate block-rotate-ccw]
       [f-= block=?]
       [f-move block-move]))
    
    ; https://github.com/samth/var/blob/master/examples/tetris-modules/bset.rkt
    (,modl-data
     ,modl-block•
     ,modl-list-fun
     ,modl-bset
     ,modl-consts
     ,(opaque
       `(module H
          (provide
           [f0 ((,c/bset ,c/block ↦ (flat bool?)) ↦ ,c/any)]
           [f1 ((,c/bset ,c/bset ↦ (flat bool?)) ↦ ,c/any)]
           [f2 ((,c/bset ↦ (flat real?)) ↦ ,c/any)]
           [f3 ((,c/bset ,c/bset ↦ ,c/bset) ↦ ,c/any)]
           [f4 ((,c/bset ↦ (flat bool?)) ↦ ,c/any)]
           [f-blocks-move (((flat real?) (flat real?) ,c/bset ↦ ,c/bset) ↦ ,c/any)]
           [f-rotate ((,c/posn ,c/bset ↦ ,c/bset) ↦ ,c/any)]
           [f-blocks-change-color ((,c/bset ,c/color ↦ ,c/bset) ↦ ,c/any)]
           [f-blocks-row ((,c/bset (flat real?) ↦ ,c/bset) ↦ ,c/any)]
           [f-full-row? ((,c/bset (flat real?) ↦ (flat bool?)) ↦ ,c/any)]
           [f-blocks-union ((,c/bset ,c/bset ↦ ,c/bset) ↦ ,c/any)])
          (require data)))
     (require H bset)
     (begin
       #;[f0 blocks-contains?]
       #;[f1 blocks-subset?]
       #;[f1 blocks=?]
       #;[f2 blocks-count]
       #;[f3 blocks-intersect]
       #;[f4 blocks-overflow?]
       #;[f-blocks-move blocks-move]
       #;[f-rotate blocks-rotate-ccw]
       #;[f-rotate blocks-rotate-cw]
       #;[f-blocks-change-color blocks-change-color]
       #;[f-blocks-change-color blocks-change-color]
       #;[f-full-row? full-row?]
       #;[f-blocks-row blocks-row]
       #;[f-blocks-union blocks-union]
       [f2 blocks-max-x]
       [f2 blocks-max-y]
       [f2 blocks-min-x]))
    
    ; https://github.com/samth/var/blob/master/examples/tetris-modules/data.rkt
    (,modl-data
     ,(opaque
       `(module H
          (provide
           [f-block (((flat nat?) (flat nat?) ,c/color ↦ ,c/block) ↦ ,c/any)]
           [f-block? ((,c/any ↦ (flat bool?)) ↦ ,c/any)]
           [f-tetra? ((,c/any ↦ (flat bool?)) ↦ ,c/any)]
           [f-world? ((,c/any ↦ (flat bool?)) ↦ ,c/any)]
           [f-block-x ((,c/block ↦ (flat nat?)) ↦ ,c/any)]
           [f-block-y ((,c/block ↦ (flat nat?)) ↦ ,c/any)]
           [f-block-color ((,c/block ↦ ,c/color) ↦ ,c/any)]
           [f-tetra ((,c/posn ,c/bset ↦ ,c/tetra) ↦ ,c/any)]
           [f-tetra-center ((,c/tetra ↦ ,c/posn) ↦ ,c/any)]
           [f-tetra-blocks ((,c/tetra ↦ ,c/bset) ↦ ,c/any)]
           [f-world ((,c/tetra ,c/bset ↦ ,c/world) ↦ ,c/any)]
           [f-world-tetra ((,c/world ↦ ,c/tetra) ↦ ,c/any)]
           [f-world-blocks ((,c/world ↦ ,c/bset) ↦ ,c/any)])
          (require data)))
     (require data H)
     (begin
       [f-world-blocks world-blocks]
       [f-world-tetra world-tetra]
       [f-world world]
       [f-world? world?]
       [f-tetra tetra]
       [f-tetra-center tetra-center]
       [f-tetra-blocks tetra-blocks]
       [f-tetra? tetra?]
       [f-block block]
       [f-block? block?]
       [f-block-color block-color]
       [f-block-x block-x]
       [f-block-y block-y]))
    
    ; https://github.com/samth/var/blob/master/examples/tetris-modules/elim-row.rkt
    (,modl-data
     ,modl-consts•
     ,modl-bset•
     ,modl-elim-row
     (module H
       (provide
        [b ,c/bset]
        [n (flat nat?)])
       (require data)
       (define b •)
       (define n •))
     (require elim-row H)
     (elim-row b n n))
    
    ; https://github.com/samth/var/blob/master/examples/tetris-modules/elim.rkt
    (,modl-data
     ,modl-consts•
     ,modl-bset•
     ,modl-elim-row•
     (module elim
       (provide
        [eliminate-full-rows (,c/bset ↦ ,c/bset)])
       (require data bset consts elim-row)
       ;; eliminate-full-rows : BSet -> BSet
       ;; Eliminate all full rows and shift down appropriately.
       (define (eliminate-full-rows bs)
         (elim-row bs board-height 0)))
     (module H
       (provide
        [b ,c/bset])
       (define b •))
     (require elim H)
     (eliminate-full-rows b))
    
    ; https://github.com/samth/var/blob/master/examples/tetris-modules/tetras.rkt
    (,modl-data
     ,modl-consts•
     ,modl-bset•
     ,modl-tetras
     ,(opaque
       `(module H
          (provide
           [n (flat nat?)]
           [t ,c/tetra]
           [f-tetra-move (((flat nat?) (flat nat?) ,c/tetra ↦ ,c/tetra) ↦ ,c/any)]
           [f-tetra-rotate-ccw ((,c/tetra ↦ ,c/tetra) ↦ ,c/any)]
           [f-tetra-rotate-cw ((,c/tetra ↦ ,c/tetra) ↦ ,c/any)]
           [f-tetra-overlaps-blocks? ((,c/tetra ,c/bset ↦ (flat bool?)) ↦ ,c/any)]
           [f-build-tetra-blocks ((,c/color (flat nat?)
                                            (flat nat?)
                                            (flat nat?)
                                            (flat nat?)
                                            (flat nat?)
                                            (flat nat?)
                                            (flat nat?)
                                            (flat nat?)
                                            (flat nat?)
                                            (flat nat?)
                                            ↦ 
                                            ,c/tetra) ↦ ,c/any)]
           [f-tetra-change-color ((,c/tetra ,c/color ↦ ,c/tetra) ↦ ,c/any)])
          (require data)))
     (require H tetras)
     (begin
       #;[f-tetra-move tetra-move]
       #;[f-tetra-change-color tetra-change-color]
       #;[f-tetra-rotate-cw tetra-rotate-cw]
       #;[f-tetra-rorate-ccw tetra-rotate-ccw]
       [f-tetra-overlaps-blocks? tetra-overlaps-blocks?]
       [f-build-tetra-blocks build-tetra-blocks]))
    
    ; https://github.com/samth/var/blob/master/examples/tetris-modules/visual.rkt
    (,modl-data
     ,modl-consts•
     ,modl-list-fun
     ,modl-world•
     ,modl-image
     (module visual
       (provide
        [world->image (,c/world ↦ (flat image?))]
        [blocks->image (,c/bset ↦ (flat image?))]
        [block->image (,c/block ↦ (flat image?))]
        [place-block (,c/block (flat image?) ↦ (flat image?))])
       (require image data consts world list-fun)
       
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
         (make-world (list-pick-random tetras) empty)))
     ,(opaque
       `(module H
          (provide
           [f-world->image ((,c/world ↦ (flat image?)) ↦ ,c/any)]
           [bs ,c/bset]
           [b ,c/block]
           [w ,c/world])
          (require data image)))
     (require H visual image)
     (f-world->image world->image))
    
    ; https://github.com/samth/var/blob/master/examples/tetris-modules/world.rkt
    ; TODO
    ))

(for-each
 (λ (t) (print (time (eval-cek t))) (display "\n\n"))
 tests)
