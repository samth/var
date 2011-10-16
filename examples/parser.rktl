#lang var ;trace

(module char? (anything -> bool?) •)

;; opaque structures
(module parse-position? (anything -> bool?) •)
(module parse-results?  (anything -> bool?) •)

(module top-parse-position 
  (string? -> parse-position?)
  •)

(module update-parse-position 
  (parse-position? char? -> parse-position?)
  •)

(module empty-results
  ((or/c parse-position? false?) -> parse-results?)
  •)

(module make-results
  ((or/c parse-position? false?)
   (or/c false? (cons/c anything anything))
   (-> parse-results?)
   -> 
   parse-results?)
  •)

(module make-error-expected
  ((or/c parse-position? false?) anything -> parse-error?)
  •)

(module make-error-message
  ((or/c parse-position? false?) string? -> parse-error?)
  •)
  
(module m string? "f")

(empty-results #f)
#;m