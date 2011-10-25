#lang racket
(require "trace.rkt" "annotate.rkt" "eval.rkt" "lang.rkt" "step.rkt"
         (prefix-in c: "cesk.rkt")
         (prefix-in f: "cesk-fast.rkt")
         redex/reduction-semantics)
(require (prefix-in rho: "rho/trace.rkt")
         (prefix-in rho: "rho/annotate.rkt"))
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
                                           (term (annotator [m (... ...) e])))))))]))

(begin-for-syntax 
  (define-syntax-class verifier-opt
    [pattern (~datum cesk)
             #:attr sym 'cesk]
    [pattern (~datum cesk-trace)
             #:attr sym 'cesk-trace]
    [pattern (~datum fast-trace)
             #:attr sym 'fast-trace]
    [pattern (~datum fast)
             #:attr sym 'fast]
    [pattern (~datum trace)
             #:attr sym 'trace]
    [pattern (~datum count)
             #:attr sym 'count]
    [pattern (~datum rho-trace)
             #:attr sym 'rho-trace]))

(define-syntax (#%module-begin stx)
  (syntax-parse stx
    [(_ (~and m ((~datum module) . _)) ...)
     #`(r:#%module-begin 
        (set-box! the-module-context '(m ...)))]
    [(_ (~optional kw:verifier-opt #:defaults ([kw.sym #f]))
        m ... e)
     #`(r:#%module-begin
        ((dynamic-require 'redex 'reduction-steps-cutoff) 100)
        (set-box! the-module-context '(m ...))        
        #,(case (attribute kw.sym) 
            [(trace)
             #'(begin (define the-program (term (annotator [m ... e])))
                      (trace-it -->_vcc~Δ the-program))
             ;;#:pp (λ (x) (pretty-format/write (term (unann-exp ,x)) 50)))
             ]
            [(rho-trace)
             #'(begin (define the-program (term (rho:annotator [m ... e])))
                      (rho:trace-it rho:-->_vcme the-program))]
            [(count)             
             #'(begin (define the-program (term (annotator [m ... e])))
                      (let ([k 0]) 
                        (count-it the-program k)
                        (printf "~a terms explored\n" k)))]
            [(cesk-trace)             
             #'(begin (define the-program (term (annotator [m ... e])))
                      (c:trace-it the-program))]
            [(fast-trace)
             #'(begin (define the-program (term (annotator [m ... e])))
                      (f:trace-it the-program))]
            [(cesk)
             #'(begin (define the-program (term (annotator [m ... e])))
                      (apply values
                             (filter-not
                              (λ (p)
                                (match p
                                  [(list (list 'blame '★ _ (... ...)) _ (... ...)) #t]
                                  [_ #f]))
                              (c:final the-program))))]
            [(fast)
             
             #'(begin (define the-program (term (annotator [m ... e])))
                      (apply values
                             (filter-not
                              (λ (p)
                                (match p
                                  [(f:st (list 'blame '★ _ (... ...)) _ _ _) #t]
                                  [_ #f]))
                              (f:step-fixpoint the-program))))]
            [else              
             #'(begin (define the-program (term (annotator [m ... e])))
                      (apply values
                             (map clean-up
                                  (filter-not
                                   (λ (p)
                                     (match p
                                       [(list 'blame '★ _ (... ...)) #t] [_ #f]))
                                   (map (λ (x) x #;(term (unann-exp ,x)))   
                                        (eval_vcc~Δ  the-program))))))]))]))

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
     
  
