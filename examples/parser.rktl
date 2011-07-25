#lang s-exp "../verified.rkt" ;trace

(module char? (anything -> bool?) •)

(module parse-position? 
  (anything -> bool?) 
  •)

(module top-parse-position 
  (string? -> (pred parse-position?)) 
  •)

(module update-parse-position 
  ((pred parse-position?) (pred char?) -> (pred parse-position?))
  •)

(module empty-results
  ((or/c (pred parse-position?) false?) -> (pred parse-results?))
  •)

(module make-results
  ((or/c (pred parse-position?) false?)
   (or/c false? (cons/c anything anything))
   (-> (pred parse-results?))
   -> 
   (pred parse-results?))
  •)

(module make-error-expected
  ((or/c (pred parse-position?) false?) anything -> (pred parse-error?))
  •)

(module make-error-message
  ((or/c (pred parse-position?) false?) string? -> (pred parse-error?))
  •)
  
(module m string? "f")

#;(empty-results #f)
m