#lang racket
(require "trace.rkt" "annotate.rkt" "eval.rkt" "lang.rkt" "step.rkt" "util.rkt"
         (prefix-in c: "cesk.rkt")
         (prefix-in f: "cesk-fast.rkt")
         redex/reduction-semantics)
(require (prefix-in rho: "rho/run.rkt")
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
  (define-syntax-class run-opt
    [pattern (~datum cesk) #:attr sym 'cesk]
    [pattern (~datum rho) #:attr sym 'rho]
    [pattern (~datum count) #:attr sym 'count]
    [pattern (~datum fast) #:attr sym 'fast]
    [pattern (~datum subst) #:attr sym 'subst])
  (define-syntax-class exact-opt
    [pattern (~datum exact) #:attr sym #t]
    [pattern (~datum approx) #:attr sym #f])
  (define-syntax-class trace-opt
    [pattern (~datum step) #:attr sym 'step]
    [pattern (~datum trace) #:attr sym 'trace]
    [pattern (~datum eval) #:attr sym 'eval]))

(define-for-syntax (finish-values op prog [extract #'values])
  #`(apply values
           (filter-not (match-lambda [(app #,extract (list 'blame '★ _ (... ...))) #t] [_ #f])
                       (#,op #,prog))))

(define-syntax (#%module-begin stx)
  (syntax-parse stx    
    [(_ (~and m ((~datum module) . _)) ...)
     #`(r:#%module-begin 
        (set-box! the-module-context '(m ...)))]
    [(_ (~optional run:run-opt #:defaults ([run.sym 'subst]))
        (~optional trace:trace-opt #:defaults ([trace.sym 'eval]))
        (~optional exact:exact-opt #:defaults ([exact.sym #t]))
        m ... e)
     (define run (attribute run.sym))
     (define trace (attribute trace.sym))
     (define exact? (attribute exact.sym))
     #`(r:#%module-begin
        ((dynamic-require 'redex 'reduction-steps-cutoff) 100)
        (set-box! the-module-context '(m ...))
        (current-exact? #,exact?)
        #,(case run
            [(rho)
             #`(begin 
                 (define the-program (term (rho:annotator [m ... e])))
                 (#,(case trace
                      [(trace) #'rho:trace-it]
                      [(step)  #'rho:step-it] 
                      [(eval)  #'rho:eval-it])
                  rho:-->_vcme the-program))]
            [(subst)
             #`(begin
                 (define the-program (term (annotator [m ... e])))
                 #,(case trace
                     [(trace) #'(trace-it -->_vcc~Δ the-program)]
                     [(step)  #'(step-it -->_vcc~Δ the-program)]
                     [(eval) (finish-values #'(λ (p) (map clean-up (eval_vcc~Δ p)))
                                            #'the-program)]))]
            [(count)             
             #'(begin 
                 (define the-program (term (annotator [m ... e])))
                 (let ([k 0]) 
                   (count-it the-program k)
                   (printf "~a terms explored\n" k)))]
            [(cesk)
             #`(begin 
                 (define the-program (term (annotator [m ... e])))
                 #,(case trace
                     [(trace) #'(c:trace-it the-program)]
                     [(step) #'(c:step-it the-program)]
                     [(eval) (finish-values #'c:final 
                                            #'the-program
                                            #'first)]))]
            [(fast) 
             #`(begin 
                 (define the-program (term (annotator [m ... e])))
                 #,(case trace
                     [(trace) #'(f:trace-it the-program)]
                     [(step) #'(f:step-it the-program)]
                     [(eval) (finish-values #'f:step-fixpoint
                                            #'the-program
                                            #'f:st-c)]))]))]))

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
     
  
