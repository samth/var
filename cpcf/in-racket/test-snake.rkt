#lang racket

(require "scpcf-lang.rkt")
(require "scpcf-eval.rkt")

(define DIRS '("up" "down" "left" "right"))

(define c/posn `(cons/c (flat real?) (flat real?)))
(define c/dir `(one-of/c ,@ DIRS))
(define c/snake `(cons/c ,c/dir ,(c/non-empty-list-of c/posn)))
(define c/world `(cons/c ,c/snake ,c/posn))

(define module-image
  `(module image
     (provide
      [image? (,c/any ↦ (flat bool?))]
      [circle ((flat real?) (flat string?) (flat string?) ↦ (flat image?))]
      [empty-scene ((flat real?) (flat real?) ↦ (flat image?))]
      [place-image ((flat image?) (flat real?) (flat real?) (flat image?) ↦ (flat image?))])
     (define image? •)
     (define circle •)
     (define empty-scene •)
     (define place-image •)))

(define module-data
  `(module data
     (provide
      [posn ((flat real?) (flat real?) ↦ ,c/posn)]
      [posn? (,c/any ↦ (flat bool?))]
      [posn-x (,c/posn ↦ (flat real?))]
      [posn-y (,c/posn ↦ (flat real?))]
      [posn=? (,c/posn ,c/posn ↦ (flat bool?))]
      [snake (,c/dir (cons/c ,c/posn ,(c/list-of c/posn)) ↦ ,c/snake)]
      [snake? (,c/any ↦ (flat bool?))]
      [snake-dir (,c/snake ↦ ,c/dir)]
      [snake-segs (,c/snake ↦ (cons/c ,c/posn ,(c/list-of c/posn)))]
      [world (,c/snake ,c/posn ↦ ,c/world)]
      [world? (,c/any ↦ (flat bool?))]
      [world-snake (,c/world ↦ ,c/snake)]
      [world-food (,c/world ↦ ,c/posn)])
     
     (define posn cons)
     (define (posn? x)
       (and (cons? x) (nat? (car x)) (nat? (cdr x))))
     (define posn-x car)
     (define posn-y cdr)
     (define (posn=? p1 p2)
       (and (= (posn-x p1) (posn-x p2))
            (= (posn-y p1) (posn-y p2))))
     
     (define snake cons) 
     (define (snake? x)
       (and (cons? x)
            (dir? (car x))
            ((non-empty-list-of posn?) (cdr x))))
     (define snake-dir car)
     (define snake-segs cdr)
     (define (dir? x)
       (or ,@ (map (λ (v) `(equal? ,v x)) DIRS)))
     
     (define world cons)
     (define (world? x)
       (and (cons? x)
            (snake? (car x))
            (posn? (cdr x))))
     (define world-snake car)
     (define world-food cdr)
     
     (define (non-empty-list-of pred?)
       (λ (x)
         (and (cons? x)
              (pred? (car x))
              ((list-of pred?) (cdr x)))))
     
     (define (list-of pred?)
       (μ (f)
          (λ (x)
            (or (nil? x)
                (and (cons? x)
                     (pred? (car x))
                     (f (cdr x)))))))))

(define module-const
  `(module const
     (provide
      [WORLD (↦ ,c/world)]
      [BACKGROUND (↦ (flat image?))]
      [FOOD-IMAGE (↦ (flat image?))]
      [SEGMENT-IMAGE (↦ (flat image?))]
      [GRID-SIZE (flat nat?)]
      [BOARD-HEIGHT-PIXELS (↦ (flat nat?))]
      [BOARD-WIDTH (flat nat?)]
      [BOARD-HEIGHT (flat nat?)])
     (require image data)
     
     (define GRID-SIZE 30)
     (define BOARD-HEIGHT 20)
     (define BOARD-WIDTH 30)
     (define (BOARD-HEIGHT-PIXELS) (* GRID-SIZE BOARD-HEIGHT))
     (define (BOARD-WIDTH-PIXELS) (* GRID-SIZE BOARD-WIDTH))
     (define (BACKGROUND) (empty-scene (BOARD-WIDTH-PIXELS) (BOARD-HEIGHT-PIXELS)))
     (define (SEGMENT-RADIUS) (quot GRID-SIZE 2))
     (define (SEGMENT-IMAGE)  (circle (SEGMENT-RADIUS) "solid" "red"))
     (define (FOOD-RADIUS) (SEGMENT-RADIUS))
     (define (FOOD-IMAGE)  (circle (FOOD-RADIUS) "solid" "green"))
     (define (WORLD) (world (snake "right" (cons (posn 5 3) nil))
                            (posn 8 12)))))

(define module-collide
  `(module collide
     (provide
      [snake-wall-collide? (,c/snake ↦ (flat bool?))]
      [snake-self-collide? (,c/snake ↦ (flat bool?))])
     (require data const)
     
     ;; snake-wall-collide? : Snake -> Boolean
     ;; Is the snake colliding with any of the walls?
     (define (snake-wall-collide? snk)
       (head-collide? (car (snake-segs snk))))
     
     ;; head-collide? : Posn -> Boolean
     (define (head-collide? p)
       (or (≤ (posn-x p) 0)
           (≥ (posn-x p) BOARD-WIDTH)
           (≤ (posn-y p) 0)
           (≥ (posn-y p) BOARD-HEIGHT)))
     
     ;; snake-self-collide? : Snake -> Boolean
     (define (snake-self-collide? snk)
       (segs-self-collide? (car (snake-segs snk))
                           (cdr (snake-segs snk))))
     
     ;; segs-self-collide? : Posn Segs -> Boolean
     (define (segs-self-collide? h segs)
       (cond [(nil? segs) #f]
             [else
              (or (posn=? (car segs) h)
                  (segs-self-collide? h (cdr segs)))]))))

(define module-cut-tail
  `(module cut-tail
     (provide
      [cut-tail (,(c/non-empty-list-of c/posn) ↦ ,(c/list-of c/posn))])
     (require data)
     ;; NeSegs is one of:
     ;; - (cons Posn empty)
     ;; - (cons Posn NeSegs)
     
     ;; cut-tail : NeSegs -> Segs
     ;; Cut off the tail.
     (define (cut-tail segs)
       (let ([r (cdr segs)])
         (cond [(nil? r) nil]
               [else
                (cons (car segs)
                      (cut-tail r))])))))

(define module-cut-tail•
  `(module cut-tail
     (provide
      [cut-tail (,(c/non-empty-list-of c/posn) ↦ ,(c/list-of c/posn))])
     (require data)
     (define cut-tail •)))

(define module-motion-help
  `(module motion-help
     (provide
      [snake-slither (,c/snake ↦ ,c/snake)]
      [snake-grow (,c/snake ↦ ,c/snake)])
     (require data cut-tail)
     
     ;; next-head : Posn Direction -> Posn
     ;; Compute next position for head.
     (define (next-head seg dir)
       (cond [(str=? "right" dir) (posn (add1 (posn-x seg)) (posn-y seg))]
             [(str=? "left" dir)  (posn (sub1 (posn-x seg)) (posn-y seg))]
             [(str=? "down" dir)  (posn (posn-x seg) (sub1 (posn-y seg)))]
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
                      (snake-segs snk)))))))

(define module-motion
  `(module motion
     (provide
      [world-change-dir (,c/world ,c/dir ↦ ,c/world)]
      [world->world (,c/world ↦ ,c/world)])
     (require data const motion-help)
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
              #;(posn (random BOARD-WIDTH) (random BOARD-HEIGHT))
              (posn (- BOARD-WIDTH 1) (- BOARD-HEIGHT 1))))))

(define tests
  `(
    ; https://github.com/samth/var/blob/master/examples/snake-modules/collide.rkt
    (,module-image
     ,module-data
     ,module-const
     ,module-collide
     (module H
       (provide
        [D ((,c/snake ↦ (flat bool?)) ↦ ,c/any)])
       (require data)
       (define D •))
     (require collide H)
     (begin [D snake-wall-collide?]
            [D snake-self-collide?]))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/const.rkt
    (,module-image
     ,module-data
     ,module-const
     (module hole
       (provide [f (,c/any ↦ ,c/any)])
       (define f •))
     (require const hole)
     (begin [f WORLD]
            [f BACKGROUND]
            [f FOOD-IMAGE]
            [f SEGMENT-IMAGE]
            [f GRID-SIZE]
            [f BOARD-HEIGHT-PIXELS]
            [f BOARD-WIDTH]
            [f BOARD-HEIGHT]))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/cut-tail.rkt
    (,module-data
     ,module-cut-tail
     (module H
       (provide
        [f ((,(c/non-empty-list-of c/posn) ↦ ,(c/list-of c/posn)) ↦ ,c/any)])
       (require data)
       (define f •))
     (require cut-tail H)
     (f cut-tail))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/data.rkt
    (,module-data
     (module D
       (provide
        [f-posn (((flat real?) (flat real?) ↦ ,c/posn) ↦ ,c/any)]
        [f-posn? ((,c/any ↦ (flat bool?)) ↦ ,c/any)]
        [f-posn-x ((,c/posn ↦ (flat real?)) ↦ ,c/any)]
        [f-posn-y ((,c/posn ↦ (flat real?)) ↦ ,c/any)]
        [f-posn=? ((,c/posn ,c/posn ↦ (flat bool?)) ↦ ,c/any)]
        [f-snake ((,c/dir (cons/c ,c/posn ,(c/list-of c/posn)) ↦ ,c/snake) ↦ ,c/any)]
        [f-snake? ((,c/any ↦ (flat bool?)) ↦ ,c/any)]
        [f-snake-dir ((,c/snake ↦ ,c/dir) ↦ ,c/any)]
        [f-snake-segs ((,c/snake ↦ ,(c/non-empty-list-of c/posn)) ↦ ,c/any)]
        [f-world ((,c/snake ,c/posn ↦ ,c/world) ↦ ,c/any)]
        [f-world? ((,c/any ↦ (flat bool?)) ↦ ,c/any)]
        [f-world-snake ((,c/world ↦ ,c/snake) ↦ ,c/any)]
        [f-world-food ((,c/world ↦ ,c/posn) ↦ ,c/any)])
       (require data)
       (define f-posn •)
       (define f-posn? •)
       (define f-posn-x •)
       (define f-posn-y •)
       (define f-posn=? •)
       (define f-snake •)
       (define f-snake? •)
       (define f-snake-dir •)
       (define f-snake-segs •)
       (define f-world •)
       (define f-world? •)
       (define f-world-snake •)
       (define f-world-food •))
     (require D data)
     (begin [f-posn posn]
            [f-posn? posn?]
            [f-posn-x posn-x]
            [f-posn-y posn-y]
            [f-posn=? posn=?]
            [f-snake snake]
            [f-snake? snake?]
            [f-snake-dir snake-dir]
            [f-snake-segs snake-segs]
            [f-world world]
            [f-world? world?]
            [f-world-snake world-snake]
            [f-world-food world-food]))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/handlers.rkt
    (,module-image
     ,module-data
     
     (module collide
       (provide
        [snake-wall-collide? (,c/snake ↦ (flat bool?))]
        [snake-self-collide? (,c/snake ↦ (flat bool?))])
       (require data)
       (define snake-wall-collide? •)
       (define snake-self-collide? •))
     
     (module motion
       ;; motion left opaque
       (provide
        [world-change-dir (,c/world ,c/dir ↦ ,c/world)]
        [world->world (,c/world ↦ ,c/world)])
       (require data)
       (define world-change-dir •)
       (define world->world •))
     
     (module handlers
       ;; Movie handlers
       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       (provide
        [handle-key (,c/world (flat string?) ↦ ,c/world)]
        [game-over? (,c/world ↦ (flat bool?))])
       (require data motion collide)
       
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
             (snake-self-collide? (world-snake w)))))
     
     (module H
       (provide
        [D1 ((,c/world ↦ (flat bool?)) ↦ ,c/any)]
        [D2 ((,c/world (flat string?) ↦ ,c/world) ↦ ,c/any)])
       (require data)
       (define D1 •)
       (define D2 •))
     
     (require handlers H)
     (begin [D1 game-over?]
            [D2 handle-key]))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/motion-help.rkt
    (,module-image
     ,module-data
     ,module-cut-tail•
     ,module-motion-help
     
     (module H
       (provide
        [f ((,c/snake ↦ ,c/snake) ↦ ,c/any)])
       (require data)
       (define f •))
     (require motion-help H)
     (begin [f snake-slither]
            [f snake-grow]))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/motion-small.rkt
    (,module-image
     ,module-data
     ,module-const
     ,module-cut-tail•
     (module motion-help
       (provide
        [snake-slither (,c/snake ↦ ,c/snake)]
        [snake-grow (,c/snake ↦ ,c/snake)])
       (require data cut-tail)
       (define snake-slither •)
       (define snake-grow •))
     ,module-motion
     (module H
       (provide
        [f1 ((,c/world ↦ ,c/world) ↦ ,c/any)]
        [f2 ((,c/world ,c/dir ↦ ,c/world) ↦ ,c/any)])
       (require data)
       (define f1 •)
       (define f2 •))
     (require motion H)
     (begin [f1 world->world]
            [f2 world-change-dir]))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/motion-split.rkt
    (,module-image
     ,module-data
     ,module-const
     ,module-cut-tail•
     ,module-motion-help
     ,module-motion
     (module H
       (provide
        [f1 ((,c/world ,c/dir ↦ ,c/world) ↦ ,c/any)]
        [f2 ((,c/world ↦ ,c/world) ↦ ,c/any)]
        [f3 ((,c/snake ↦ ,c/snake) ↦ ,c/any)]
        [d ,c/dir]
        [p ,c/posn]
        [lop ,(c/non-empty-list-of c/posn)]
        [w ,c/world]
        [s ,c/snake])
       (require data)
       (define f1 •)
       (define f2 •)
       (define f3 •)
       (define d •)
       (define p •)
       (define lop •)
       (define w •)
       (define s •))
     (require motion H slither grow) ; ??
     (begin [world-change-dir w d]))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/motion.rkt
    (,module-image
     ,module-data
     ,module-const
     ,module-cut-tail•
     ,module-motion-help
     ,module-motion
     (module hole
       (provide
        [f1 ((,c/world ,c/dir ↦ ,c/world) ↦ ,c/any)]
        [f2 ((,c/world ↦ ,c/world) ↦ ,c/any)]
        [f3 ((,c/snake ↦ ,c/snake) ↦ ,c/any)])
       (require data)
       (define f1 •)
       (define f2 •)
       (define f3 •))
     (require motion hole slither)
     (begin [f1 world-change-dir]
            [f2 world->world]))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/scenes.rkt
    (,module-image
     ,module-data
     ,module-const
     (module scenes
       
       (provide
        [world->scene (,c/world ↦ (flat image?))]
        [food+scene (,c/posn (flat image?) ↦ (flat image?))]
        [place-image-on-grid
         ((flat image?) (flat real?) (flat real?) (flat image?) ↦ (flat image?))]
        [snake+scene (,c/snake (flat image?) ↦ (flat image?))]
        [segments+scene (,(c/list-of c/posn) (flat image?) ↦ (flat image?))]
        [segment+scene (,c/posn (flat image?) ↦ (flat image?))])
       (require data const image)
       
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
         (cond [(nil? segs) scn]
               [else (segments+scene (cdr segs) ;; tail recursion
                                     (segment+scene (car segs) scn))]))
       
       ;; segment+scene : Posn Image -> Image
       ;; Add one snake segment to a scene.
       (define (segment+scene seg scn)
         (place-image-on-grid (SEGMENT-IMAGE) (posn-x seg) (posn-y seg) scn)))
     
     (module hole
       (provide
        [f ((,c/world ↦ (flat image?)) ↦ ,c/any)])
       (require data image)
       (define f •))
     (require scenes hole)
     (f world->scene))
    
    ; https://github.com/samth/var/blob/master/examples/snake-modules/slither.rkt
    (,module-data
     ,module-cut-tail
     ,module-motion-help
     (module S
       (provide
        [S ,c/snake]
        [L ,(c/non-empty-list-of c/posn)]
        [L2 ,(c/list-of c/posn)])
       (require data)
       (define S •)
       (define L •)
       (define L2 •))
     (require S motion-help)
     (begin [snake-slither S]
            #;[reverse L2 L2]
            #;[cut-tail/acc L L2]))))

(for-each
 (λ (t) (print (time (eval-cek t))) (display "\n\n"))
 tests)