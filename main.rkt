#lang racket
(require "run.rkt" "annotate.rkt" "meta.rkt" "cesk.rkt" "lang.rkt" "util.rkt"
         redex/reduction-semantics racket/list)
(require (for-syntax syntax/parse racket/syntax))
(require (prefix-in r: (only-in racket/base #%module-begin)))
(provide #%module-begin #%top-interaction)
(require unstable/pretty)
(provide clean-up)
(define the-module-context (box null))


(begin-for-syntax 
  (define/with-syntax the-program (generate-temporary 'the-program))
  (define-syntax-class run-opt
    [pattern (~datum cesk) #:attr sym 'cesk]
    [pattern (~datum rho) #:attr sym 'rho]
    #;[pattern (~datum count) #:attr sym 'count]
    #;[pattern (~datum fast) #:attr sym 'fast])
  (define-syntax-class exact-opt
    [pattern (~datum exact) #:attr sym #t]
    [pattern (~datum approx) #:attr sym #f])
  (define-syntax-class trace-opt
    [pattern (~datum step) #:attr sym 'step]
    [pattern (~datum trace) #:attr sym 'trace]
    [pattern (~datum eval) #:attr sym 'eval])
  (define-syntax-class direct-opt
    [pattern (~datum direct) #:attr sym #t]
    [pattern (~datum indirect) #:attr sym #f]))

(define-syntax (#%top-interaction stx)  
  (syntax-parse stx
    [(_ . e)
     #`(let ([ctxt (unbox the-module-context)])
         #,(finish-values #'(λ (x) (eval-it ---> x))
                          #'(term (annotator [,@ctxt e]))
                          #'first))]))

(define-for-syntax (finish-values op prog [extract #'values])
  #`(apply values
           (filter-not (match-lambda [(app #,extract (list 'blame '★ _ (... ...))) #t] [_ #f])
                       (#,op #,prog))))

(define-syntax (#%module-begin stx)
  ;; (printf "#%module-begin starting ~a\n" (current-process-milliseconds))
  (syntax-parse stx    
    [(_ (~and m ((~datum module) . _)) ...)
     #`(r:#%module-begin 
        (set-box! the-module-context '(m ...)))]
    [(_ (~optional run:run-opt #:defaults ([run.sym 'rho]))
        (~optional trace:trace-opt #:defaults ([trace.sym 'eval]))
        (~optional exact:exact-opt #:defaults ([exact.sym #t]))
        (~optional direct:direct-opt #:defaults ([direct.sym #t]))
        m ... e)
     (define run (attribute run.sym))
     (define trace (attribute trace.sym))
     (define exact? (attribute exact.sym))
     (define direct? (attribute direct.sym))
     #`(r:#%module-begin
        ; (printf "module starting ~a\n" (current-process-milliseconds))
        #,(if (memq trace '(trace step))
              #'(reduction-steps-cutoff 100)
              #'(void))
        (set-box! the-module-context '(m ...))
        (current-exact? #,exact?)
        (initial-char-width 140)
        (define the-program (term (annotator [m ... e])))
        #,(case run
            [(rho)             
             #`(begin  
                 (current-direct? #,direct?)
                 #,(case trace
                     [(trace) #'(trace-it ---> the-program)]
                     [(step)  #'(step-it ---> the-program)] 
                     [(eval)  (finish-values #'(λ (x) (eval-it ---> x))
                                             #'the-program
                                             #'first)]))]            
            #;
            [(count)             
             #'(begin 
                 (let ([k 0]) 
                   (count-it the-program k)
                   (printf "~a terms explored\n" k)))]
            [(cesk)
             #`(begin
                 ;; Always redirect through store for CESK machine.
                 (current-direct? #f)
                 #,(case trace
                     [(trace) #'(CESK-trace-it the-program)]
                     [(step) #'(step-it CESK the-program)]
                     [(eval) (finish-values #'CESK-run
                                            #'the-program
                                            #'first)]))]))]))

(define (clean-up r)
  (match r
    [(list '-- c-or-v c ...)
     (if (redex-match λcρ PREVAL c-or-v)
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
     
  
