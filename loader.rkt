#lang racket
(require "lang/reader.rkt"
         "annotate.rkt"
         redex/reduction-semantics)
(provide load-program) 

(define (load-program path)  ; Path -> Prog
  (define p (open-input-file path))  
  (parameterize ((read-accept-lang #t))
    (read-language p)
    (begin0 (term (annotator ,(cddr (fourth (read p 'var 0 0 0)))))
            (close-input-port p))))
  