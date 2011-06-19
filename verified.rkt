#lang racket
(require "trace.rkt" "annotate.rkt" "eval.rkt" redex)
(require (for-syntax syntax/parse))
(require (prefix-in r: (only-in racket/base #%module-begin)))
(provide #%module-begin #%top-interaction)
(require unstable/pretty)

(define-syntax (#%module-begin stx)
  (syntax-parse stx
    [(_ (~optional (~and tr (~datum trace))) m ... e)
     #`(r:#%module-begin 
        (parameterize ([reduction-steps-cutoff 100]) 
          ;(step-it -->_vcc~Δ (term (ann [m ... e])))
          #,(if (attribute tr)
                 #'(trace-it -->_vcc~Δ (term (ann/define-contract [m ... e])))    
                   ;;#:pp (λ (x) (pretty-format/write (term (unann-exp ,x)) 50)))
                 #'(apply values
                          (filter-not
                           (λ (p)
                             (match p
                               [(list 'blame '★ _ (... ...)) #t] [_ #f]))
                           (map (λ (x) x #;(term (unann-exp ,x)))   
                                (eval_vcc~Δ  (term (ann/define-contract [m ... e])))))))))]))
        