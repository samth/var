#lang var ;trace

(define/contract char? (-> anything boolean?) •)

;; opaque structures
(define/contract parse-position? (-> anything boolean?) •)
(define/contract parse-results?  (-> anything boolean?) •)

(define/contract top-parse-position 
  (-> string? parse-position?)
  •)

(define/contract update-parse-position 
  (-> parse-position? char? parse-position?)
  •)

(define/contract empty-results
  (-> (or/c parse-position? false?) parse-results?)
  •)

(define/contract make-results
  (-> (or/c parse-position? false?)
      (or/c false? (cons/c anything anything))
      (-> parse-results?)   
      parse-results?)
  •)

(define/contract make-error-expected
  (-> (or/c parse-position? false?) anything parse-error?)
  •)

(define/contract make-error-message
  (-> (or/c parse-position? false?) string? parse-error?)
  •)
  
(define/contract m string? "f")

(require 'empty-results)

(empty-results #f)
#;m