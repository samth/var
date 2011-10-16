#lang racket
(require "trace.rkt" "annotate.rkt" "eval.rkt" "lang.rkt" (prefix-in c: "cesk.rkt") redex "step.rkt")
(require (for-syntax syntax/parse))
(require (prefix-in r: (only-in racket/base #%module-begin)))
(provide #%module-begin #%top-interaction)
(require unstable/pretty)
(provide clean-up)
(define the-module-context (box null))

(define-syntax (#%top-interaction stx)  
  (syntax-parse stx
    [(_ . e)
     #'(apply values
              (map clean-up
                   (filter-not
                    (λ (p)
                      (match p
                        [(list 'blame '★ _ (... ...)) #t] [_ #f]))
                    (eval_vcc~Δ  (term-let ([(m (... ...)) (unbox the-module-context)])
                                           (term (ann/define-contract [m (... ...) e])))))))]))

(define-syntax (#%module-begin stx)
  (syntax-parse stx
    [(_ (~and m ((~datum module) . _)) ...)
	#`(r:#%module-begin 
	   (set-box! the-module-context '(m ...)))]
    [(_ (~optional (~and kw (~or (~datum cesk) (~datum cesk-trace) (~datum trace) (~datum count)))) m ... e)
     #`(r:#%module-begin 
        (parameterize ([reduction-steps-cutoff 100]) 
          (set-box! the-module-context '(m ...))
          ;(step-it -->_vcc~Δ (term (ann [m ... e])))
          #,(begin
              (cond 
                [(and (attribute kw)
                      (eq? (syntax-e (attribute kw)) 'trace))
                 #'(trace-it -->_vcc~Δ (term (ann/define-contract [m ... e])))  
                 ;;#:pp (λ (x) (pretty-format/write (term (unann-exp ,x)) 50)))
                 ]
                [(and (attribute kw)
                      (eq? (syntax-e (attribute kw)) 'count))
                 #'(let ([k 0]) 
                     (count-it (term (ann/define-contract [m ... e])) k)
                     (printf "~a terms explored\n" k))]
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
                          (map clean-up
                                (filter-not
                                 (λ (p)
                                   (match p
                                     [(list 'blame '★ _ (... ...)) #t] [_ #f]))
                                 (map (λ (x) x #;(term (unann-exp ,x)))   
                                      (eval_vcc~Δ  (term (ann/define-contract [m ... e])))))))]))))]))

(define (clean-up r)
  (match r
    [(list '-- c-or-v c ...)
     (if (redex-match λc~ PV c-or-v)
         c-or-v     
         (cons '● (remove-duplicates (filter-map clean-up-c (cons c-or-v c)))))]
    [(list 'blame f g v0 c v1)
     (list 'blame f g (clean-up v0) (clean-up-c c) (clean-up v1))]
    [_ r]))

(define (clean-up-c c)
  (match c
    [`(pred (λ (,x) #t) ,l) #f]
    [(list 'pred (list (and (? symbol?) f) '^ _) _)
     (list 'pred f)]
    [(list 'pred (list-rest l) _)
     (list 'pred l)]
    [_ c]))
     
  
