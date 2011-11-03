#lang racket/load
(module data racket 
  (struct posn (x y))
  (struct snake (dir segs))
  (struct world (snake food))
  
  ;; direction? : Any -> Boolean
  ;; Is s a direction?
  (define (direction? s)
    (and (string? s)
         (or (string=? s "up")
             (string=? s "down")
             (string=? s "left")
             (string=? s "right"))))
  
  ;; posn=? : Posn Posn -> Boolean
  ;; Are the posns the same?
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2))))  
  
  (provide/contract 
   [direction? (any/c . -> . boolean?)]
   [posn (exact-nonnegative-integer? exact-nonnegative-integer? . -> . posn?)]
   [posn? (any/c . -> . boolean?)]
   [posn-x (posn? . -> . exact-nonnegative-integer?)]
   [posn-y (posn? . -> . exact-nonnegative-integer?)]
   [posn=? (posn? posn? . -> . boolean?)]
   [snake (direction? (cons/c posn? (listof posn?)) . -> . snake?)]
   [snake? (any/c . -> . boolean?)]
   [snake-dir (snake? . -> . direction?)]
   [snake-segs (snake? . -> . (non-empty-listof posn?))]
   [world (snake? posn? . -> . world?)]
   [world? (any/c . -> . boolean?)]
   [world-snake (world? . -> . snake?)]
   [world-food (world? . -> . posn?)]))
  
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
  (require 2htdp/image 'data)  
  
  ;; --- CONSTANTS : DESCRIBE PROPERTIES THAT ARE ALWAYS THE SAME 
 
  (define GRID-SIZE 30) ; width of a game-board square
  (define BOARD-HEIGHT 20) ; height in grid squares
  (define BOARD-WIDTH  30) ; width  in grid squares
  (define BOARD-HEIGHT-PIXELS (* GRID-SIZE BOARD-HEIGHT))
  (define BOARD-WIDTH-PIXELS  (* GRID-SIZE BOARD-WIDTH))
  
  (define BACKGROUND (empty-scene BOARD-WIDTH-PIXELS BOARD-HEIGHT-PIXELS))
  
  (define SEGMENT-RADIUS (quotient GRID-SIZE 2))
  (define SEGMENT-IMAGE  (circle SEGMENT-RADIUS "solid" "red"))
  
  (define FOOD-RADIUS SEGMENT-RADIUS)
  (define FOOD-IMAGE  (circle FOOD-RADIUS "solid" "green"))
  
  (define SNAKE (snake "right" (cons (posn 5 3) empty)))
  (define FOOD  (posn 8 12))
  (define WORLD (world SNAKE FOOD))
  
  (provide/contract [WORLD world?]
                    [BACKGROUND image?]
                    [FOOD-IMAGE image?]
                    [SEGMENT-IMAGE image?]
                    [GRID-SIZE exact-nonnegative-integer?]
                    [BOARD-HEIGHT-PIXELS exact-nonnegative-integer?]
                    [BOARD-WIDTH exact-nonnegative-integer?]
                    [BOARD-HEIGHT exact-nonnegative-integer?]))

(module scenes racket
  (require 2htdp/image) 
  (require 'data 'const)
    
  ;; Image-painting functions
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;; world->scene : World -> Image
  ;; Build an image of the given world.
  (define (world->scene w) 
    (snake+scene (world-snake w) 
                 (food+scene (world-food w) BACKGROUND)))
   
  ;; food+scene : Food Image -> Image 
  ;; Add image of food to the given scene.
  (define (food+scene f scn)
    (place-image-on-grid FOOD-IMAGE (posn-x f) (posn-y f) scn))
  
  ;; place-image-on-grid : Image Number Number Image -> Image
  ;; Just like PLACE-IMAGE, but use grid coordinates.
  (define (place-image-on-grid img x y scn)
    (place-image img
                 (* GRID-SIZE x)
                 (- BOARD-HEIGHT-PIXELS (* GRID-SIZE y))
                 scn))
  
  ;; snake+scene : Snake Image -> Image 
  ;; Add an image of the snake to the scene.
  (define (snake+scene snk scn)
    (segments+scene (snake-segs snk) scn))
  
  ;; segments+scene : Segs Image -> Image 
  ;; Add an image of the snake segments to the scene.
  (define (segments+scene segs scn) 
    (cond [(empty? segs) scn]
          [else (segment+scene (first segs)              
                               (segments+scene (rest segs) scn))]))
  
  ;; segment+scene : Posn Image -> Image
  ;; Add one snake segment to a scene.
  (define (segment+scene seg scn)
    (place-image-on-grid SEGMENT-IMAGE (posn-x seg) (posn-y seg) scn))
  
  (provide/contract
   [world->scene (world? . -> . image?)]
   [food+scene (posn? image? . -> . image?)]
   [place-image-on-grid 
    (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]
   [snake+scene (snake? image? . -> . image?)]
   [segments+scene ((listof posn?) image? . -> . image?)]
   [segment+scene (posn? image? . -> . image?)])
  
  )

(module motion racket
  (require 'data 'const)  
  
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
            (first (snake-segs (world-snake w)))))
  
  ;; snake-slither : Snake -> Snake
  (define (snake-slither snk)
    (snake (snake-dir snk)                                                       
           (cons (next-head (first (snake-segs snk))
                            (snake-dir snk))
                 (cut-tail (snake-segs snk)))))
   
  ;; next-head : Posn Direction -> Posn
  ;; Compute next position for head.
  (define (next-head seg dir)
    (cond [(string=? "right" dir) (posn (add1 (posn-x seg)) (posn-y seg))]
          [(string=? "left" dir)  (posn (sub1 (posn-x seg)) (posn-y seg))]
          [(string=? "down" dir)  (posn (posn-x seg) (sub1 (posn-y seg)))]
          [else                   (posn (posn-x seg) (add1 (posn-y seg)))]))
    
  ;; NeSegs is one of:
  ;; - (cons Posn empty)
  ;; - (cons Posn NeSegs)
  
  ;; cut-tail : NeSegs -> Segs
  ;; Cut off the tail.
  (define (cut-tail segs) 
    (cond [(empty? (rest segs)) empty]
          [else
           (cons (first segs)
                 (cut-tail (rest segs)))]))
    
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
    
  ;; snake-grow : Snake -> Snake
  ;; Grow the snake one segment.
  (define (snake-grow snk)
    (snake (snake-dir snk)                                                       
           (cons (next-head (first (snake-segs snk))
                            (snake-dir snk))
                 (snake-segs snk))))
  
  (provide/contract [world-change-dir (world? direction? . -> . world?)]
                    [world->world (world? . -> . world?)]))

(module collide racket  
  (require 'data 'const)
  
  ;; Collisions
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;; snake-wall-collide? : Snake -> Boolean
  ;; Is the snake colliding with any of the walls?
  (define (snake-wall-collide? snk)
    (head-collide? (first (snake-segs snk))))
  
  ;; head-collide? : Posn -> Boolean
  (define (head-collide? p)
    (or (<= (posn-x p) 0)
        (>= (posn-x p) BOARD-WIDTH)
        (<= (posn-y p) 0)
        (>= (posn-y p) BOARD-HEIGHT)))
 
  ;; snake-self-collide? : Snake -> Boolean
  (define (snake-self-collide? snk)
    (segs-self-collide? (first (snake-segs snk))
                        (rest (snake-segs snk))))
  
  ;; segs-self-collide? : Posn Segs -> Boolean
  (define (segs-self-collide? h segs)
    (cond [(empty? segs) false]
          [else
           (or (posn=? (first segs) h)
               (segs-self-collide? h (rest segs)))]))
    
  (provide/contract [snake-wall-collide? (snake? . -> . boolean?)]
                    [snake-self-collide? (snake? . -> . boolean?)]))

(module handlers racket
  (require 'data 'motion 'collide)
  
  ;; Movie handlers
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;; handle-key : World String -> World
  (define (handle-key w ke) 
    (cond [(string=? ke "w") (world-change-dir w "up")]
          [(string=? ke "s") (world-change-dir w "down")]
          [(string=? ke "a") (world-change-dir w "left")]
          [(string=? ke "d") (world-change-dir w "right")]
          [else w]))
  
  ;; game-over? : World -> Boolean
  (define (game-over? w)
    (or (snake-wall-collide? (world-snake w))
        (snake-self-collide? (world-snake w))))
  
  (provide/contract [handle-key (world? string? . -> . world?)]
                    [game-over? (world? . -> . boolean?)]))

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
(start WORLD)
