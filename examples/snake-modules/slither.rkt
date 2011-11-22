#lang var cesk

(define-contract posn/c (struct/c posn exact-nonnegative-integer? exact-nonnegative-integer?))
(define-contract direction/c #;symbol? (one-of/c 'up 'down 'left 'right))
(define-contract snake/c
  (struct/c snake
            direction/c
            (non-empty-listof posn/c)))

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
   [snake-segs (snake/c . -> . (non-empty-listof posn/c))]))

(module cut-tail racket
  (require 'data)
    
  ;; NeSegs is one of:
  ;; - (cons Posn empty)
  ;; - (cons Posn NeSegs)
  
  ;; cut-tail : NeSegs -> Segs
  ;; Cut off the tail.
  #;
  (define (cut-tail segs) 
    (cond [(empty? (cdr segs)) empty]
          [else
           (cons (car segs)
                 (cut-tail (cdr segs)))]))
  
  (provide/contract [cut-tail ((non-empty-listof posn/c) . -> . (listof posn/c))]))

(module slither racket
  (require 'data 'cut-tail)
  
  ;; snake-slither : Snake -> Snake
  (define (snake-slither snk)
    (let ([d (snake-dir snk)])
      (snake d
             (cons (next-head (car (snake-segs snk))
                              d)
                   (cut-tail (snake-segs snk))))))
   
  ;; next-head : Posn Direction -> Posn
  ;; Compute next position for head.
  (define (next-head seg dir)
    (cond [(symbol=? 'right dir) (posn (add1 (posn-x seg)) (posn-y seg))]
          [(symbol=? 'left dir)  (posn (sub1 (posn-x seg)) (posn-y seg))]
          [(symbol=? 'down dir)  (posn (posn-x seg) (sub1 (posn-y seg)))]
          [else                  (posn (posn-x seg) (add1 (posn-y seg)))]))
    
  
  (provide/contract [snake-slither (snake/c . -> . snake/c)]))

(module S racket
  (require 'data)
  (provide/contract [S snake/c]
                    [L (non-empty-listof posn/c)]
                    [L2 (listof posn/c)]))

(require 'S 'slither)

(snake-slither S)
#;
(begin #;(cut-tail L)
       (reverse L2 L2)
       #;
       (cut-tail/acc L L2))