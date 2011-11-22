#lang var cesk

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

(module collide racket
  (require 'data)
  (provide/contract [snake-wall-collide? (snake/c . -> . boolean?)]
                    [snake-self-collide? (snake/c . -> . boolean?)]))


(module motion racket
  (require 'data)
  ;; motion left opaque
  (provide/contract [world-change-dir (world/c direction/c . -> . world/c)]
                    [world->world (world/c . -> . world/c)])
)

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

(module H racket
  (require 'data)
  (provide/contract [D1 ((world/c . -> . boolean?) . -> . any/c)]
                    [D2 ((world/c string? . -> . world/c) . -> . any/c)]))

(require 'handlers 'H)

(begin
  (D1 game-over?)
  (D2 handle-key))

