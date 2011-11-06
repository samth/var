#lang racket/load

;; -- Primitive modules
(module image racket
  (require 2htdp/image) ;; COMMENT OUT THIS LINE
  (provide/contract
   [image? (any/c . -> . boolean?)]
   [circle (exact-nonnegative-integer? (one-of/c 'outline 'solid) symbol? . -> . image?)]
   [line (exact-nonnegative-integer? exact-nonnegative-integer? symbol? . -> . image?)]
   [rotate (exact-nonnegative-integer? image? . -> . image?)]
   [text (string? exact-nonnegative-integer? symbol? . -> . image?)]
   [empty-scene (exact-nonnegative-integer? exact-nonnegative-integer? . -> . image?)]
   [place-image (image? exact-nonnegative-integer? exact-nonnegative-integer? image? . -> . image?)]))

(module prims racket
  ;; string->chars : String -> [Listof String]
  ;; Turn a String into a list of single char Strings
  (define (string->chars s)
    (map string (string->list s)))    
  (provide/contract
   [length ((or/c cons? empty?) . -> . exact-nonnegative-integer?)]
   [string-append (string? string? . -> . string?)]
   [string->chars (string? . -> . (listof string?))]))

;; -- Source

(module hangman racket
  (require 'prims)
  
  ;; A World is a (world String [Listof String])
  (struct world (secret guesses))

  (define (foldr f b ls)
    (if (empty? ls) b
        (f (car ls) (foldr f b (cdr ls)))))
  
  (define (foldl f b ls)
    (if (empty? ls) b
        (foldl f (f (car ls) b) (cdr ls))))
  
  ;; FIXME contract specific to this programs use of filter.
  ;; [String -> Boolean] [Listof String] -> [Listof String]
  (define (filter f ls)
    (if (empty? ls) empty
        (if (f (car ls))
            (cons (car ls) (filter f (cdr ls)))
            (filter f (cdr ls)))))
  
  ;; String [Listof String] -> Boolean
  (define (string-member x ls)
    (if (empty? ls) #f
        (or (string=? (car ls) x)
            (string-member x (cdr ls)))))

  ;; fill-in-the-blanks : [Listof String] [Listof String] -> String
  ;; Replace missing letters with blanks, add spaces for visual appeal
  (define (fill-in-the-blanks secret guessed)
    (foldl (λ (c str)
             (string-append str
                            (string-append (cond [(zero? (string-length str)) ""]
                                                 [else " "])
                                           (cond [(string-member c guessed) c]
                                                 [else "_"]))))                                           
           ""
           secret))
  
  ;(define sec (string->chars "guess"))
  ;(check-expect (fill-in-the-blanks sec empty) "_ _ _ _ _")
  ;(check-expect (fill-in-the-blanks sec (list "g")) "g _ _ _ _")
  ;(check-expect (fill-in-the-blanks sec (list "s" "g")) "g _ _ s s")
  
  ;; reveal : World -> String
  ;; Construct a string with that reveals what has been guessed of the secret.
  (define (reveal w)
    (fill-in-the-blanks (string->chars (world-secret w))
                        (world-guesses w)))
  
  ;; [Listof String] -> [Listof String]
  ;; Delete all duplicates from the list.
  ;(check-expect (delete-dups (list "a" "a" "b"))
  ;              (list "a" "b"))
  (define (delete-dups xs)
    (foldr (λ (x xs)
             (cond [(string-member x xs) xs]
                   [else (cons x xs)]))
           empty
           xs))
  
  ;; count-matches : [String -> Boolean] World -> Number
  ;; Count the number of matching guesses (right or wrong).
  (define (count-matches pred w)
    (length (filter pred (world-guesses w))))
  
  ;; make-right-? : World -> [String -> Boolean]
  ;; Create a predicate for right guesses
  (define (make-right-? w)
    (let ((sec (string->chars (world-secret w))))
      (λ (c)
        (string-member c sec))))
  
  ;; make-wrong-? : World -> [String -> Boolean]
  ;; Create a predicate for wrong guesses
  (define (make-wrong-? w)
    (let ((sec (string->chars (world-secret w))))
      (λ (c)
        (not (string-member c sec)))))
  
  ;(define world1 (world "guess" (string->chars "xysuz")))
  ;(check-expect (count-matches (make-wrong-? world1) world1) 3)
  ;(check-expect (count-matches (make-right-? world1) world1) 2)
  
  
  ;; game-over : World -> Boolean
  ;; Have too many guesses been made or the secret been guessed?
  (define (game-over? w)
    (or (= 7 (count-matches (make-wrong-? w) w))
        (= (length (delete-dups (string->chars (world-secret w))))
           (count-matches (make-right-? w) w))))
  
  ;(check-expect (game-over? (world "guess" (list "q" "r" "t" "v"
  ;                                                    "x" "y" "z"))) true)
  ;(check-expect (game-over? (world "guess" (list "s" "e" "u" "g"))) true)
  ;(check-expect (game-over? (world "guess" empty)) false)
  
  ;; handle-key : World KeyEvent -> World
  ;; Handle keys; if a char, use it as a guess.
  (define (handle-key w ke)
    (cond [(= (string-length ke) 1)
           (world (world-secret w)
                  (delete-dups (cons ke (world-guesses w))))]
          [else w]))
  
  ;(check-expect (handle-key (world "guess" empty) "a")
  ;              (world "guess" (list "a")))
  ;(check-expect (handle-key (world "guess" empty) "up")
  ;              (world "guess" empty))
  
  (provide/contract
   [handle-key ((struct/c world string? (listof string?)) string? . -> . (struct/c world string? (listof string?)))]
   [game-over? ((struct/c world string? (listof string?)) . -> . boolean?)]
   [reveal ((struct/c world string? (listof string?)) . -> . string?)]
   [count-matches ((string? . -> . boolean?) 
                   (struct/c world string? (listof string?)) 
                   . -> .
                   exact-nonnegative-integer?)]
   [make-wrong-? ((struct/c world string? (listof string?)) . -> . (string? . -> . boolean?))]
   [make-right-? ((struct/c world string? (listof string?)) . -> . (string? . -> . boolean?))]
   
   (struct world ([secret string?] 
                  [guesses (listof string?)]))
   ;[world (string? (listof string?) . -> . (struct/c world string? (listof string?)))]
   ;[world-secret ((struct/c world string? (listof string?)) . -> . string?)]
   ;[world-guesses ((struct/c world string? (listof string?)) . -> . (listof string?))]
   ))

(module render racket
  (require 'hangman 'image)

  ;; Rendering system defined constants
  (define SCENE-HEIGHT 500)
  (define SCENE-WIDTH 400)  
  (define RIGHT-LIMB (line 50 50 'red))
  (define LEFT-LIMB (rotate 90 RIGHT-LIMB))
  (define GALLOWS-IMG 
    (place-image (line 0 50 'blue)
                 200 75
                 (place-image (line 150 0 'blue)
                              125 50
                              (place-image (line 0 300 'blue)
                                           50 200
                                           (empty-scene SCENE-WIDTH 
                                                        SCENE-HEIGHT)))))
  
  ;; add-* : Image -> Image
  ;; Add a {head,body,right/left-arm/leg,dead-eyes} to scene.
  (define (add-head scn)
    (place-image (circle 30 'solid 'red) 200 100 scn))
  
  (define (add-body scn)
    (place-image (line 0 150 'red) 200 175 scn))
  
  (define (add-right-arm scn)
    (place-image RIGHT-LIMB 225 175 scn))
  
  (define (add-left-arm scn)
    (place-image LEFT-LIMB 175 175 scn))
  
  (define (add-left-leg scn)
    (place-image LEFT-LIMB 175 275 scn))
  
  (define (add-right-leg scn)
    (place-image RIGHT-LIMB 225 275 scn))
  
  (define (add-dead-eyes scn)
    (let ((img (text "X X" 20 'black)))
      (place-image img 200 100 scn)))
  
  ;; draw-hangman : Number -> Image
  ;; Draw the hangman after i wrong guesses.
  (define (draw-hangman i)
    (cond [(= 0 i) GALLOWS-IMG]
          [(= 1 i) (add-head      (draw-hangman 0))]
          [(= 2 i) (add-body      (draw-hangman 1))]
          [(= 3 i) (add-left-arm  (draw-hangman 2))]
          [(= 4 i) (add-right-arm (draw-hangman 3))]
          [(= 5 i) (add-left-leg  (draw-hangman 4))]
          [(= 6 i) (add-right-leg (draw-hangman 5))]
          [else    (add-dead-eyes (draw-hangman 6))]))
  
  ;(check-expect (draw-hangman 0) GALLOWS-IMG)
  ;(check-expect (draw-hangman 7)
  ;              (add-dead-eyes
  ;               (add-right-leg
  ;                (add-left-leg
  ;                 (add-right-arm
  ;                  (add-left-arm
  ;                   (add-body
  ;                    (add-head GALLOWS-IMG))))))))
      
  ;; render : World -> Image
  ;; Render the world as a scene.
  (define (render w)
    (let ((img (text (reveal w) 30 'red)))
      (place-image img
                   (quotient SCENE-WIDTH 2)
                   (- SCENE-HEIGHT 50)
                   (draw-hangman (count-matches (make-wrong-? w) w)))))
  
  (provide/contract 
   [render ((struct/c world string? (listof string?)) . -> . image?)]))

(module play racket
  (require 2htdp/universe)
  (require 'render 'hangman)
  (provide play)
  (define (play s)
    (big-bang (world s empty)
              (on-key handle-key)
              (on-draw render)
              (stop-when game-over?))))
