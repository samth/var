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

(module H racket
  (require 'data)
  (provide/contract [D ((snake/c . -> . boolean?) . -> . any/c)]))

(require 'collide 'H)
(begin (D snake-wall-collide?)
       (D snake-self-collide?))