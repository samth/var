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

(module cut-tail racket
  (require 'data)

  ;; NeSegs is one of:
  ;; - (cons Posn empty)
  ;; - (cons Posn NeSegs)

  ;; cut-tail : NeSegs -> Segs
  ;; Cut off the tail.
  #;
  (define (cut-tail segs)
    (let ([r (cdr segs)])
      (cond [(empty? r) empty]
            [else
             (cons (car segs)
                   (cut-tail r))])))
  
  (provide/contract [cut-tail ((non-empty-listof posn/c) . -> . (listof posn/c))]))

(module next-head racket
  (require 'data)

  ;; next-head : Posn Direction -> Posn
  ;; Compute next position for head.
  #;
  (define (next-head seg dir)
    (cond [(symbol=? 'right dir) (posn (add1 (posn-x seg)) (posn-y seg))]
          [(symbol=? 'left dir)  (posn (sub1 (posn-x seg)) (posn-y seg))]
          [(symbol=? 'down dir)  (posn (posn-x seg) (sub1 (posn-y seg)))]
          [else                  (posn (posn-x seg) (add1 (posn-y seg)))]))

  (provide/contract [next-head (posn/c direction/c . -> . posn/c)])

  )

(module slither racket
  (require 'data 'next-head 'cut-tail)

  ;; snake-slither : Snake -> Snake
  #;
  (define (snake-slither snk)
    (let ([d (snake-dir snk)])
      (snake d
             (cons (next-head (car (snake-segs snk))
                              d)
                   (cut-tail (snake-segs snk))))))
  (provide/contract [snake-slither (snake/c . -> . snake/c)])
  )

(module grow racket
  (require 'data 'next-head)

  ;; snake-grow : Snake -> Snake
  ;; Grow the snake one segment.
  #;
  (define (snake-grow snk)
    (let ([d (snake-dir snk)])
      (snake d
             (cons (next-head (car (snake-segs snk))
                              d)
                   (snake-segs snk)))))
  (provide/contract [snake-grow (snake/c . -> . snake/c)])
  )


(module motion racket
  (require 'data 'const 'slither 'grow)
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

(module H racket
  (require 'data)
  (provide/contract [f1 ((world/c direction/c . -> . world/c) . -> . any/c)]
                    [f2 ((world/c . -> . world/c) . -> . any/c)]
                    [f3 ((snake/c . -> . snake/c) . -> . any/c)]
                    [d direction/c]
                    [p posn/c]
                    [lop (non-empty-listof posn/c)]
                    [w world/c]
                    [s snake/c]))

(require 'motion 'H 'slither 'grow)
#;
(begin #;(f1 world-change-dir)
       #;(f3 snake-slither)
       #;(f2 world->world))
;
(begin
   (world-change-dir w d)
  ;; (world->world w)
  ;; (cut-tail lop)
  #;(snake-grow s)
  #;(snake-slither s)
  #;(next-head p d))
