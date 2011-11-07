#lang racket/load
;; -- Primitive module
(module prims racket
  (require 2htdp/image)
  (provide/contract 
   [image? (any/c . -> . boolean?)]
   [rectangle (exact-nonnegative-integer? exact-nonnegative-integer?
                                          (one-of/c 'solid 'outline)
                                          (one-of/c 'red) 
                                          . -> . image?)]   
   [text (string? exact-nonnegative-integer? (one-of/c 'black) . -> . image?)]
   [image-height (image? . -> . exact-nonnegative-integer?)]
   [image-width (image? . -> . exact-nonnegative-integer?)]
   [empty-scene (exact-nonnegative-integer? exact-nonnegative-integer? . -> . image?)]
   [line (exact-nonnegative-integer? exact-nonnegative-integer? (one-of/c 'red) . -> . image?)]
   [beside (image? image? . -> . image?)]
   [overlay/align (one-of/c 'left) (one-of/c 'middle) image? image? . -> . image?]))
                    
;; -- Source

(module data racket
  
  ;; A 1String is a string, s, whose length is exactly one, 
  ;; i.e. (= (string-length s) 1). 
  
  ;; A list of 1Strings (Lo1String) is one of:
  ;; - empty
  ;; - (cons 1String Lo1String)
  
  (struct editor (pre post))
  ;; An Editor is a (editor Lo1String Lo1String)
    
  ;; String -> Boolean
  (define (1string? s)
    (= 1 (string-length s)))
    
  (provide/contract 
   [1string? (string? . -> . boolean?)]
   (struct editor
     ([pre (listof (and/c string? 1string?))]
      [post (listof (and/c string? 1string?))]))))
                                         

(module const racket
  (require 'prims)
  
  ;; The insight is that pre should represent the editors to the 
  ;; left of the cursor in right to left order.
  ;; It's not necessary to have this insight to get full credit,
  ;; but it makes it easier to do so.  For students who didn't
  ;; get this, make a note of it for them.
  
  ;; Constants
  (define FONT-SIZE 20)
  (define CURSOR-SIZE 25)  
  (define WIDTH 300)
  (define HEIGHT 33)
  
  (provide/contract
   [FONT-SIZE exact-nonnegative-integer?]
   [CURSOR-SIZE exact-nonnegative-integer?]
   [WIDTH exact-nonnegative-integer?]
   [HEIGHT exact-nonnegative-integer?]))

(module editor racket
  (require 'prims 'const 'data)
  
  ;(define Hello_^There 
  ;  (editor (list " " "o" "l" "l" "e" "H")
  ;               (list "T" "h" "e" "r" "e")))
  
  ;; Editor -> Image
  ;; Render the editor as an image.
  (define (render e)
    (beside (text (lo1string->string (reverse (editor-pre e))) FONT-SIZE 'black)
            (beside (line 0 CURSOR-SIZE 'red)
                    (text (lo1string->string (editor-post e)) FONT-SIZE 'black))))
  
  ;(check-expect (render Hello_^There)
  ;              (overlay/xy (text "Hello There" FONT-SIZE "black")
  ;                          (cursor-x "Hello ")
  ;                          (quotient (image-height CURSOR) 2)
  ;                          CURSOR))
  
  ;; Lo1String -> String
  ;; Convert a list of 1Strings to a String
  (define (lo1string->string ls)
    (cond [(empty? ls) ""]
          [else (string-append (car ls)
                               (lo1string->string (cdr ls)))]))
  
  ;(check-expect (lo1string->string (list "H" "e" "l" "l" "o"))
  ;              "Hello")

  ;; String -> Lo1String
  ;; Convert a String to a list of 1Strings.
  (define (string->lo1string str)
    (cond [(string=? str "") empty]
          [else
           (cons (substring str 0 1)
                 (string->lo1string (substring str 1 (string-length str))))]))
  
  ;(check-expect (string->lo1string "Hello")
  ;              (list "H" "e" "l" "l" "o"))
  
  ;; String -> Number
  ;; Compute the x-coord of the cursor if placed after str.
  (define (cursor-x str)
    (image-width (text str FONT-SIZE 'black)))
 
  ;(check-expect (cursor-x "") 0)
  ;(check-expect (cursor-x "H")
  ;              (image-width (text "H" FONT-SIZE "black")))
  
  ;; ----------------------------------------------------------------
  ;; Editor -> Scene
  ;; Render the edtior as a scene.
  (define (editor->scene e)
    (overlay/align 'left 'middle
                   (render e)
                   (empty-scene WIDTH HEIGHT)))
  
  ;(check-expect (editor->scene Hello_^There)
  ;              (place-image (render Hello_^There)
  ;                           PADDING PADDING
  ;                           (empty-scene WIDTH HEIGHT)))
  
  ;; ----------------------------------------------------------------
  ;; Editor String -> Editor
  ;; Enter a key in the editor.
  ;(check-expect (edit.v0 Hello_^There 'left)
  ;              (left Hello_^There))
  ;(check-expect (edit.v0 Hello_^There 'right)
  ;              (right Hello_^There))
  ;(check-expect (edit.v0 Hello_^There #\backspace)
  ;              (backspace Hello_^There))
  ;(check-expect (edit.v0 Hello_^There #\x)
  ;              (type Hello_^There #\x))
  ;(check-expect (edit.v0 Hello_^There 'up)
  ;              Hello_^There)
  (define (edit e k)
    (cond [(1string? k) 
           (cond [(string=? k "\r") e]
                 [(string=? k "\b") (backspace e)]
                 [(string=? k "\t") e]
                 [else (type e k)])]
          [(string=? k "left") (left e)]
          [(string=? k "right") (right e)]
          [else k]))
  

          

  ;; Editor -> Editor
  ;; Move the cursor left.
  ;(check-expect (left (editor empty (list "f" "o" "o")))
  ;              (editor empty (list "f" "o" "o")))
  ;(check-expect (left (editor (list "o" "o" "f") (list "b" "a" "r")))
  ;              (editor (list "o" "f") (list "o" "b" "a" "r")))
  (define (left e)
    (cond [(empty? (editor-pre e)) e]
          [else
           (editor (cdr (editor-pre e))
                        (cons (car (editor-pre e))
                              (editor-post e)))]))
  
  ;; Editor -> Editor
  ;; Move the cursor right.
  ;(check-expect (right (editor (list "o" "o" "f") empty)) 
  ;              (editor (list "o" "o" "f") empty))
  ;(check-expect (right (editor (list "o" "o" "f") (list "b" "a" "r")))
  ;              (editor (list "b" "o" "o" "f") (list "a" "r")))
  (define (right e)
    (cond [(empty? (editor-post e)) e]
          [else
           (editor (cons (car (editor-post e)) (editor-pre e))
                   (cdr (editor-post e)))]))
  
  ;; Editor -> Editor
  ;; Delete to the left of the cursor.
  ;(check-expect (backspace (editor empty (list "f" "o" "o")))
  ;              (editor empty (list "f" "o" "o")))
  ;(check-expect (backspace (editor (list "o" "o" "f") (list "b" "a" "r")))
  ;              (editor (list "o" "f") (list "b" "a" "r")))
  (define (backspace e)
    (cond [(empty? (editor-pre e)) e]
          [else
           (editor (cdr (editor-pre e))
                        (editor-post e))]))
  
  ;; Editor Char -> Editor
  ;(check-expect (type (editor (list "o" "o" "f") (list "b" "a" "r")) #\x)
  ;              (editor (list "x" "o" "o" "f") (list "b" "a" "r")))
  (define (type e s)
    (editor (cons s (editor-pre e))
            (editor-post e)))
  
  (provide/contract 
   [editor->scene ((struct/c editor 
                             (listof (and/c string? 1string?))
                             (listof (and/c string? 1string?)))
                   . -> . 
                   image?)]
   [edit ((struct/c editor 
                    (listof (and/c string? 1string?))
                    (listof (and/c string? 1string?)))
          string?
          . -> . 
          (struct/c editor 
                    (listof (and/c string? 1string?))
                    (listof (and/c string? 1string?))))]))

;; ----------------------------------------------------------------
(module start racket
  (require 'data 'const 'editor)
  (require 2htdp/universe)
  (define (start)
    (big-bang (editor empty empty)
              (to-draw editor->scene)
              (on-key edit)))
                     
  (provide start)
  )

(require 'start)
(start)



