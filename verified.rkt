#lang racket
(require "trace.rkt" "annotate.rkt" "eval.rkt" (prefix-in c: "cesk.rkt") redex)
(require (for-syntax syntax/parse))
(require (prefix-in r: (only-in racket/base #%module-begin)))
(provide #%module-begin #%top-interaction)
(require unstable/pretty)

(define-syntax (#%module-begin stx)
  (syntax-parse stx
    [(_ (~optional (~and kw (~or (~datum cesk) (~datum cesk-trace) (~datum trace)))) m ... e)
     #`(r:#%module-begin 
        (parameterize ([reduction-steps-cutoff 100]) 
          ;(step-it -->_vcc~Δ (term (ann [m ... e])))
          #,(begin
              (displayln (attribute kw))
              (cond 
                [(and (attribute kw)
                      (eq? (syntax-e (attribute kw)) 'trace))
                 #'(trace-it -->_vcc~Δ (term (ann/define-contract [m ... e])))  
                 ;;#:pp (λ (x) (pretty-format/write (term (unann-exp ,x)) 50)))
                 ]
                [(and (attribute kw)
                      (eq? (syntax-e (attribute kw)) 'cesk-trace))
                 #'(c:trace-it (term (ann/define-contract [m ... e])))]
                [(and (attribute kw)
                      (eq? (syntax-e (attribute kw)) 'cesk))
                 #'(apply values
                          (filter-not
                           (λ (p)
                             (match p
                               [(list (list 'blame '★ _ (... ...)) _ (... ...)) #t]
                               [_ #f]))
                           (c:final (term (ann/define-contract [m ... e])))))]
                [else 
                 #'(apply values
                          (filter-not
                           (λ (p)
                             (match p
                               [(list 'blame '★ _ (... ...)) #t] [_ #f]))
                           (map (λ (x) x #;(term (unann-exp ,x)))   
                                (eval_vcc~Δ  (term (ann/define-contract [m ... e]))))))]))))]))
        