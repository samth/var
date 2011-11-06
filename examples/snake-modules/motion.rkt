#lang var rho

(define-contract posn/c (struct/c posn exact-nonnegative-integer? exact-nonnegative-integer?))
(define-contract direction/c (one-of/c 'up 'down 'left 'right))
(define-contract snake/c
  (struct/c snake
            direction/c
            (non-empty-listof posn/c)))
(define-contract world/c
  (struct/c world
            snake/c
            posn/c))

(module image racket
  ;(require 2htdp/image) ;; COMMENT OUT THIS LINE
  (provide/contract
   [image? (any/c . -> . boolean?)]
   [circle (exact-nonnegative-integer? string? string? . -> . image?)]
   [empty-scene (exact-nonnegative-integer? exact-nonnegative-integer? . -> . image?)]
   [place-image (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]))

(module data racket 
  (struct posn (x y))
  (struct snake (dir segs))
  (struct world (snake food))  
  
  ;; posn=? : Posn Posn -> Boolean
  ;; Are the posns the same?
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2))))  
  
  (provide/contract 
   [posn (exact-nonnegative-integer? exact-nonnegative-integer? . -> . posn/c)]
   [posn? (any/c . -> . boolean?)]
   [posn-x (posn/c . -> . exact-nonnegative-integer?)]
   [posn-y (posn/c . -> . exact-nonnegative-integer?)]
   [posn=? (posn/c posn/c . -> . boolean?)]
   [snake (direction/c (cons/c posn/c (listof posn/c)) . -> . snake/c)]
   [snake? (any/c . -> . boolean?)]
   [snake-dir (snake/c . -> . direction/c)]
   [snake-segs (snake/c . -> . (non-empty-listof posn/c))]
   [world (snake/c posn/c . -> . world/c)]
   [world? (any/c . -> . boolean?)]
   [world-snake (world/c . -> . snake/c)]
   [world-food (world/c . -> . posn/c)]))

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
          [else (segments+scene (cdr segs) ;; tail recursion
                                (segment+scene (car segs) scn))]))
  
  ;; segment+scene : Posn Image -> Image
  ;; Add one snake segment to a scene.
  (define (segment+scene seg scn)
    (place-image-on-grid (SEGMENT-IMAGE) (posn-x seg) (posn-y seg) scn))
  
  (provide/contract
   [world->scene (world/c . -> . image?)]
   [food+scene (posn? image? . -> . image?)]
   [place-image-on-grid 
    (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]
   [snake+scene (snake/c image? . -> . image?)]
   [segments+scene ((listof posn/c) image? . -> . image?)]
   [segment+scene (posn/c image? . -> . image?)])
  
  )

(module slither racket
  (require 'data 'const)
  #|
  ;; snake-slither : Snake -> Snake
  (define (snake-slither snk)
    (snake (snake-dir snk)                                                       
           (cons (next-head (car (snake-segs snk))
                            (snake-dir snk))
                 (cut-tail (snake-segs snk)))))
   
  ;; next-head : Posn Direction -> Posn
  ;; Compute next position for head.
  (define (next-head seg dir)
    (cond [(symbol=? "right" dir) (posn (add1 (posn-x seg)) (posn-y seg))]
          [(symbol=? "left" dir)  (posn (sub1 (posn-x seg)) (posn-y seg))]
          [(symbol=? "down" dir)  (posn (posn-x seg) (sub1 (posn-y seg)))]
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
  
  (define (cut-tail/acc segs a) 
    (cond [(empty? (cdr segs)) (reverse a empty)]
          [else (cut-tail/acc (cdr segs) (cons (car segs) a))]))
  
  (define (reverse l a)
    (cond [(empty? l) empty]
          [else (reverse (cdr l) (cons (car l) a))]))
  |#
  (provide/contract [snake-slither (snake/c . -> . snake/c)]))

(module motion racket
  (require 'data 'const)  
  
  
  ;; next-head : Posn Direction -> Posn
  ;; Compute next position for head.
  (define (next-head seg dir)
    (cond [(symbol=? "right" dir) (posn (add1 (posn-x seg)) (posn-y seg))]
          [(symbol=? "left" dir)  (posn (sub1 (posn-x seg)) (posn-y seg))]
          [(symbol=? "down" dir)  (posn (posn-x seg) (sub1 (posn-y seg)))]
          [else                   (posn (posn-x seg) (add1 (posn-y seg)))]))
  
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
    
  ;; snake-grow : Snake -> Snake
  ;; Grow the snake one segment.
  (define (snake-grow snk)
    (snake (snake-dir snk)                                                       
           (cons (next-head (car (snake-segs snk))
                            (snake-dir snk))
                 (snake-segs snk))))
  
  (provide/contract [world-change-dir (world/c direction/c . -> . world/c)]
                    [world->world (world/c . -> . world/c)]))

(module hole racket
  (require 'data)
  (provide/contract [f1 ((world/c direction/c . -> . world/c) . -> . any/c)]
                    [f2 ((world/c . -> . world/c) . -> . any/c)]
                    [f3 ((snake/c . -> . snake/c) . -> . any/c)]))

(require 'motion 'hole 'slither)
(begin #;(f1 world-change-dir)
       #;(f2 snake-slither)
       (f2 world->world))
