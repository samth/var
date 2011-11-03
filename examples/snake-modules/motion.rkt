#lang var rho
(module image racket
  ;(require 2htdp/image) ;; COMMENT OUT THIS LINE
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
  
  (define (WORLD) (world (snake "right" (cons (posn 5 3) empty))
                         (posn 8 12)))
  
  (provide/contract [WORLD (-> world?)]
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
          [else (segments+scene (cdr segs) ;; tail recursion
                                (segment+scene (car segs) scn))]))
  
  ;; segment+scene : Posn Image -> Image
  ;; Add one snake segment to a scene.
  (define (segment+scene seg scn)
    (place-image-on-grid (SEGMENT-IMAGE) (posn-x seg) (posn-y seg) scn))
  
  (provide/contract
   [world->scene (world? . -> . image?)]
   [food+scene (posn? image? . -> . image?)]
   [place-image-on-grid 
    (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]
   [snake+scene (snake? image? . -> . image?)]
   [segments+scene ((listof posn?) image? . -> . image?)]))

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
            (car (snake-segs (world-snake w)))))
  
  ;; snake-slither : Snake -> Snake
  (define (snake-slither snk)
    (snake (snake-dir snk)                                                       
           (cons (next-head (car (snake-segs snk))
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
    (cond [(empty? (cdr segs)) empty]
          [else
           (cons (car segs)
                 (cut-tail (cdr segs)))]))
    
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
           (cons (next-head (car (snake-segs snk))
                            (snake-dir snk))
                 (snake-segs snk))))
  
  (provide/contract [world-change-dir (world? direction? . -> . world?)]
                    [world->world (world? . -> . world?)]))

(module hole racket
  (provide/contract [f (any/c . -> . any/c)]))

(require 'motion 'hole)
(begin (f world-change-dir)
       (f world->world))
