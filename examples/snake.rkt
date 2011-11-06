#lang racket/load
;; -- Primitive modules
(module image racket
  (require 2htdp/image) ;; COMMENT OUT THIS LINE
  (provide/contract
   [image? (any/c . -> . boolean?)]
   [circle (exact-nonnegative-integer? string? string? . -> . image?)]
   [empty-scene (exact-nonnegative-integer? exact-nonnegative-integer? . -> . image?)]
   [place-image (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]))

;; -- Source
(module data racket
  (struct posn (x y))
  (struct snake (dir segs))
  (struct world (snake food))

  ;; Contracts
  (define direction/c
    (one-of/c 'up 'down 'left 'right))
  (define posn/c
    (struct/c posn
              exact-nonnegative-integer?
              exact-nonnegative-integer?))
  (define snake/c
    (struct/c snake
              direction/c
              (non-empty-listof posn/c)))
  (define world/c
    (struct/c world
              snake/c
              posn/c))

  ;; posn=? : Posn Posn -> Boolean
  ;; Are the posns the same?
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2))))

  (provide posn/c snake/c direction/c world/c)
  (provide/contract
   [posn (exact-nonnegative-integer? exact-nonnegative-integer? . -> . posn/c)]
   [posn? (any/c . -> . boolean?)]
   [posn-x (posn/c . -> . exact-nonnegative-integer?)]
   [posn-y (posn/c . -> . exact-nonnegative-integer?)]
   [posn=? (posn/c posn/c . -> . boolean?)]
   [snake (direction/c (non-empty-listof posn/c) . -> . snake/c)]
   [snake? (any/c . -> . boolean?)]
   [snake-dir (snake/c . -> . direction/c)]
   [snake-segs (snake/c . -> . (non-empty-listof posn/c))]
   [world (snake/c posn/c . -> . world/c)]
   [world? (any/c . -> . boolean?)]
   [world-snake (world/c . -> . snake/c)]
   [world-food (world/c . -> . posn/c)]))

;; SNAKE WORLD
;;;
;; World is: (world Snake Food)
;; Food is: Posn
;; Snake is: (snake Direction Segs)
;;   A snake's Segs may not be empty.
;;   The first element of the list is the head.
;; Direction is one of: "up" "down" "left" "right"
;; Segs is one of:
;;  -- empty
;;  -- (cons Posn Segs)
;; Coordinates are in "grid" units, with X running left-to-right,
;; and Y running bottom-to-top.


(module const racket
  (require 'image 'data)

  ;; --- CONSTANTS : DESCRIBE PROPERTIES THAT ARE ALWAYS THE SAME

  (define GRID-SIZE 30) ; width of a game-board square
  (define BOARD-HEIGHT 20) ; height in grid squares
  (define BOARD-WIDTH  30) ; width  in grid squares
  (define (BOARD-HEIGHT-PIXELS) (* GRID-SIZE BOARD-HEIGHT))
  (define (BOARD-WIDTH-PIXELS)  (* GRID-SIZE BOARD-WIDTH))

  (define (BACKGROUND) (empty-scene (BOARD-WIDTH-PIXELS) (BOARD-HEIGHT-PIXELS)))

  (define (SEGMENT-RADIUS) (quotient GRID-SIZE 2))
  (define (SEGMENT-IMAGE)  (circle (SEGMENT-RADIUS) "solid" "red"))

  (define (FOOD-RADIUS) (SEGMENT-RADIUS))
  (define (FOOD-IMAGE)  (circle (FOOD-RADIUS) "solid" "green"))

  (define (WORLD) (world (snake 'right (cons (posn 5 3) empty))
                         (posn 8 12)))

  (provide/contract [WORLD (-> world/c)]
                    [BACKGROUND (-> image?)]
                    [FOOD-IMAGE (-> image?)]
                    [SEGMENT-IMAGE (-> image?)]
                    [GRID-SIZE exact-nonnegative-integer?]
                    [BOARD-HEIGHT-PIXELS (-> exact-nonnegative-integer?)]
                    [BOARD-WIDTH exact-nonnegative-integer?]
                    [BOARD-HEIGHT exact-nonnegative-integer?]))

(module scenes racket
  (require 'data 'const 'image)

  ;; Image-painting functions
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; world->scene : World -> Image
  ;; Build an image of the given world.
  (define (world->scene w)
    (snake+scene (world-snake w)
                 (food+scene (world-food w) (BACKGROUND))))

  ;; food+scene : Food Image -> Image
  ;; Add image of food to the given scene.
  (define (food+scene f scn)
    (place-image-on-grid (FOOD-IMAGE) (posn-x f) (posn-y f) scn))

  ;; place-image-on-grid : Image Number Number Image -> Image
  ;; Just like PLACE-IMAGE, but use grid coordinates.
  (define (place-image-on-grid img x y scn)
    (place-image img
                 (* GRID-SIZE x)
                 (- (BOARD-HEIGHT-PIXELS) (* GRID-SIZE y))
                 scn))

  ;; snake+scene : Snake Image -> Image
  ;; Add an image of the snake to the scene.
  (define (snake+scene snk scn)
    (segments+scene (snake-segs snk) scn))

  ;; segments+scene : Segs Image -> Image
  ;; Add an image of the snake segments to the scene.
  (define (segments+scene segs scn)
    (cond [(empty? segs) scn]
          [else (segments+scene (cdr segs) ; tail recursion
                                (segment+scene (first segs) scn))]))

  ;; segment+scene : Posn Image -> Image
  ;; Add one snake segment to a scene.
  (define (segment+scene seg scn)
    (place-image-on-grid (SEGMENT-IMAGE) (posn-x seg) (posn-y seg) scn))

  (provide/contract
   [world->scene (world/c . -> . image?)]
   [food+scene (posn/c image? . -> . image?)]
   [place-image-on-grid
    (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]
   [snake+scene (snake/c image? . -> . image?)]
   [segments+scene ((listof posn/c) image? . -> . image?)]))

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

(module motion-help racket
  (require 'data 'cut-tail)

  ;; next-head : Posn Direction -> Posn
  ;; Compute next position for head.
  (define (next-head seg dir)
    (cond [(symbol=? 'right dir) (posn (add1 (posn-x seg)) (posn-y seg))]
          [(symbol=? 'left dir)  (posn (sub1 (posn-x seg)) (posn-y seg))]
          [(symbol=? 'down dir)  (posn (posn-x seg) (sub1 (posn-y seg)))]
          [else                  (posn (posn-x seg) (add1 (posn-y seg)))]))

  ;; snake-slither : Snake -> Snake
  ;; move the snake one step
  (define (snake-slither snk)
    (let ([d (snake-dir snk)])
      (snake d
             (cons (next-head (car (snake-segs snk))
                              d)
                   (cut-tail (snake-segs snk))))))


  ;; snake-grow : Snake -> Snake
  ;; Grow the snake one segment.
  (define (snake-grow snk)
    (let ([d (snake-dir snk)])
      (snake d
             (cons (next-head (car (snake-segs snk))
                              d)
                   (snake-segs snk)))))
  (provide/contract [snake-slither (snake/c . -> . snake/c)]
                    [snake-grow (snake/c . -> . snake/c)]))

(module motion racket
  (require 'data 'const 'motion-help)

  ;; Snake motion & growth
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; world->world : World -> World
  (define (world->world w)
    (cond [(eating? w) (snake-eat w)]
          [else
           (world (snake-slither (world-snake w))
                  (world-food w))]))

  ;; eating? : World -> Boolean
  ;; Is the snake eating the food in the world.
  (define (eating? w)
    (posn=? (world-food w)
            (car (snake-segs (world-snake w)))))


  ;; snake-change-direction : Snake Direction -> Snake
  ;; Change the direction of the snake.
  (define (snake-change-direction snk dir)
    (snake dir
           (snake-segs snk)))

  ;; world-change-dir : World Direction -> World
  ;; Change direction of the world.
  (define (world-change-dir w dir)
    (world (snake-change-direction (world-snake w) dir)
           (world-food w)))

  ;; snake-eat : World -> World
  ;; Eat the food and generate a new one.
  (define (snake-eat w)
    (world (snake-grow (world-snake w))
           (posn (random BOARD-WIDTH) (random BOARD-HEIGHT))))


  (provide/contract [world-change-dir (world/c direction/c . -> . world/c)]
                    [world->world (world/c . -> . world/c)]))

(module collide racket
  (require 'data 'const)

  ;; Collisions
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; snake-wall-collide? : Snake -> Boolean
  ;; Is the snake colliding with any of the walls?
  (define (snake-wall-collide? snk)
    (head-collide? (car (snake-segs snk))))

  ;; head-collide? : Posn -> Boolean
  (define (head-collide? p)
    (or (<= (posn-x p) 0)
        (>= (posn-x p) BOARD-WIDTH)
        (<= (posn-y p) 0)
        (>= (posn-y p) BOARD-HEIGHT)))

  ;; snake-self-collide? : Snake -> Boolean
  (define (snake-self-collide? snk)
    (segs-self-collide? (car (snake-segs snk))
                        (cdr (snake-segs snk))))

  ;; segs-self-collide? : Posn Segs -> Boolean
  (define (segs-self-collide? h segs)
    (cond [(empty? segs) #f]
          [else
           (or (posn=? (car segs) h)
               (segs-self-collide? h (cdr segs)))]))

  (provide/contract [snake-wall-collide? (snake/c . -> . boolean?)]
                    [snake-self-collide? (snake/c . -> . boolean?)]))

(module handlers racket
  (require 'data 'motion 'collide)

  ;; Movie handlers
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; handle-key : World String -> World
  (define (handle-key w ke)
    (cond [(string=? ke "w") (world-change-dir w 'up)]
          [(string=? ke "s") (world-change-dir w 'down)]
          [(string=? ke "a") (world-change-dir w 'left)]
          [(string=? ke "d") (world-change-dir w 'right)]
          [else w]))

  ;; game-over? : World -> Boolean
  (define (game-over? w)
    (or (snake-wall-collide? (world-snake w))
        (snake-self-collide? (world-snake w))))

  (provide/contract [handle-key (world/c string? . -> . world/c)]
                    [game-over? (world/c . -> . boolean?)]))

(module snake racket
  (require 2htdp/universe)
  (require 'scenes 'handlers 'motion)
  ;; RUN PROGRAM RUN
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; World -> World
  (define (start w)
    (big-bang w
              (to-draw   world->scene)
              (on-tick   world->world 1/2)
              (on-key    handle-key)
              (stop-when game-over?)))
  (provide start))


(require 'snake 'const)
(start (WORLD))
