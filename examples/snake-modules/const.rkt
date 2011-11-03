#lang var rho
(module image racket
  (require 2htdp/image) ;; COMMENT OUT THIS LINE
  (provide/contract
   [image? (any/c . -> . boolean?)]
   [circle (exact-nonnegative-integer? string? string? . -> . image?)]
   [empty-scene (exact-nonnegative-integer? exact-nonnegative-integer? . -> . image?)]
   [place-image (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]))

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

(module hole racket
  (provide/contract [f (any/c . -> . any/c)]))

(require 'const 'hole)
(begin (f WORLD)
       (f BACKGROUND)
       (f FOOD-IMAGE)
       (f SEGMENT-IMAGE)
       (f GRID-SIZE)
       (f BOARD-HEIGHT-PIXELS)
       (f BOARD-WIDTH)
       (f BOARD-HEIGHT))
       