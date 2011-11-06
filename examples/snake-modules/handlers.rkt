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
