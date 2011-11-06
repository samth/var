#lang var rho

;; THIS FILE TAKES over 4k steps

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

(module cut-tail racket
  (require 'data)
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

(module H racket
  (require 'data)
  (provide/contract [f ((snake/c . -> . snake/c) . -> . any/c)]))

(require 'motion-help 'H)

(begin (f snake-slither) (f snake-grow))
