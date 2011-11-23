#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt"
         "step-v.rkt" "step-c.rkt" "step-c-abs.rkt"
         "step-m.rkt" "step-m-abs.rkt" "step-e.rkt"
         "step-a.rkt" "step-d.rkt" "garbage.rkt")
(provide (except-out (all-defined-out) test))
(provide v c c~ m m~ e a d)
(test-suite test step)

(define step-count 0)

;; A-normalization
(define-metafunction λcρ
  ev/D : D -> D
  [(ev/D A) A]
  [(ev/D (in-hole 𝓔 BLAME)) BLAME]
  [(ev/D (in-hole 𝓔 REDEX)) (in-hole 𝓔 REDEX)]
  [(ev/D (in-hole 𝓔 (clos • ρ))) (ev/D (in-hole 𝓔 (join-contracts)))]
  [(ev/D (in-hole 𝓔 PREVAL)) (ev/D (in-hole 𝓔 (-- PREVAL)))]
  [(ev/D (in-hole 𝓔 (clos (@ EXP ... LAB) ρ)))
   (ev/D (in-hole 𝓔 (@ (↓ EXP ρ) ... LAB)))]
  [(ev/D (in-hole 𝓔 (clos (@* EXP ... LAB) ρ)))
   (ev/D (in-hole 𝓔 (@* (↓ EXP ρ) ... LAB)))]  
  [(ev/D (in-hole 𝓔 (clos (if EXP ...) ρ)))
   (ev/D (in-hole 𝓔 (if (↓ EXP ρ) ...)))]  
  [(ev/D (in-hole 𝓔 (clos (let ((X EXP) ...) EXP_1) ρ)))
   (ev/D (in-hole 𝓔 (let ((X (↓ EXP ρ)) ...) (↓ EXP_1 ρ))))]
  [(ev/D (in-hole 𝓔 (clos (begin EXP EXP_1) ρ)))
   (ev/D (in-hole 𝓔 (begin (↓ EXP ρ) (↓ EXP_1 ρ))))]
  [(ev/D (in-hole 𝓔 (clos MODREF ρ)))
   (ev/D (in-hole 𝓔 MODREF))]
  [(ev/D (in-hole 𝓔 (let () D)))
   (ev/D (in-hole 𝓔 D))]
  [(ev/D (in-hole 𝓔 (ANYCON ρ <= LAB_1 LAB_2 V LAB_3 D)))
   (ev/D (in-hole 𝓔 D))])

(define (---> Ms) 
  (define r 
    (union-reduction-relations v c c~ a d (m Ms) (m~ Ms)))    
  (reduction-relation 
   λcρ #:domain (D σ) ;; runs faster if you use REDEX
   (--> ((in-hole 𝓔 REDEX) σ)
        (gc ((ev/D (in-hole 𝓔 D_contractum)) σ_1))
        (where (any_0 ... (any_name (D_contractum σ_1)) any_1 ...)
               ,(let ([r (apply-reduction-relation/tag-with-names r (term (REDEX σ)))])
                  (set! step-count (add1 step-count))                  
                  #;(when (zero? (modulo step-count 50))
                      (printf "steps: ~a, terms: ~a\n" step-count (length r))
                      #;
                      (when (not (null? r))
                        (displayln (first r))))
                  r))
        (computed-name (term any_name))
        redex!)
   (--> (D σ)
        (gc (BLAME σ))
        (where (any_0 ... (any_name (BLAME σ)) any_1 ...)
               ,(apply-reduction-relation/tag-with-names e (term (D σ))))
        (computed-name (term any_name))
        blame!)))

(test
 (define Ms 
   (term [(module m racket 
            (require) 
            (define n 7)
            (provide/contract 
             [n (pred exact-nonnegative-integer? m)]))]))
 (test/v-->> (---> Ms)
             (term (n ^ † m))
             (term (-- (↓ 7 (env))))))


(test
 (define Ms 
   ;; Factorial with type-like contract
   (term [(module f racket 
            (require) 
            (define fact 
              (λ ! (n) 
                (if (@ zero? n f) 1
                    (@ * n (@ ! (@ sub1 n f) f) f))))
            (provide/contract 
             [fact ((pred exact-nonnegative-integer? f) 
                    -> (pred exact-nonnegative-integer? f))]))]))
 (test/v-->> (---> Ms)
             (term (↓ (@ (fact ^ † f) 5 †) (env)))
             (term (-- (↓ 120 (env))))))


;; FIXME -- this is hard to express without GC.
#; 
(test
 ;; Factorial with simple dependent contract
 (define Ms 
   (term [(module f racket 
            (require) 
            (define fact 
              (λ ! (n) 
                (if (@ zero? n f) 1
                    (@ * n (@ ! (@ sub1 n f) f) f))))
            (provide/contract 
             [fact ((pred exact-nonnegative-integer? f) 
                    ->
                    (λ (x)
                      (and/c (pred exact-nonnegative-integer? f)
                             (pred (λ (y) (@ <= x y f)) f))))]))]))
 (test/v-->> (---> Ms)
             (term (↓ (@ (fact ^ † f) 5 †) (env)))
             (term (-- (↓ 120 (env))
                       ((pred (λ (y) (@ <= x y f)) f)
                        (env (x (-- (↓ 5 (env))))))))))

(test
 (test-->> (---> empty)
           (term ((↓ (@ (λ (x) 0) 1 †) (env)) (sto)))
           (redex-let λcρ
                      ([(ρ σ) (term (bind-vars (env) (sto) (x (-- (↓ 1 (env))))))])
                      (term ((-- (↓ 0 ρ)) σ))))
 (test/v-->> (---> empty)
             (term (↓ (@ (λ fact (n)
                           (if (@ zero? n †)
                               1
                               (@ * n (@ fact (@ sub1 n †) †) †)))
                         5 †)
                      (env)))
             (term (-- (↓ 120 (env)))))
 (test-->> (---> empty)
           (term ((↓ (begin 3 5) (env)) (sto)))
           (term ((-- (↓ 5 (env))) (sto))))
 (test-->> (---> empty)
           (term ((let ((x (-- (↓ 1 (env))))
                        (y (-- (↓ 2 (env)))))
                    (↓ (@ + x y †) (env)))
                  (sto)))
           (redex-let λcρ
                      ([(ρ σ) (term (bind-vars (env) (sto) 
                                               (x (-- (↓ 1 (env))))
                                               (y (-- (↓ 2 (env))))))])
                      (term ((-- (↓ 3 (env))) σ))))
 (test-->> (---> empty)
           (term ((↓ (@ procedure-arity-includes? (λ (x) x) 1 †) (env)) (sto)))
           (term ((-- (↓ #t (env))) (sto))))
 (test-->> (---> empty)
           (term ((↓ (@ procedure-arity-includes? (λ (x) x) 2 †) (env)) (sto)))
           (term ((-- (↓ #f (env))) (sto))))
 (test-->> (---> empty)
           (term ((↓ (@ (λ () 1) 2 †) (env)) (sto)))
           (term ((blame † Λ (-- (↓ (λ () 1) (env))) λ (-- (↓ (λ () 1) (env)))) (sto))))
 (test-->> (---> empty)
           (term ((↓ (@ 3 1 †) (env)) (sto)))
           (term ((blame † Λ (-- (↓ 3 (env))) λ (-- (↓ 3 (env)))) (sto)))))

(test
 (define Ms
   (term [(module p racket
            (require)
            (struct posn (x y))
            (provide/contract
             [posn ((pred exact-nonnegative-integer? p)
                    (pred exact-nonnegative-integer? p)
                    -> (pred (posn? ^ p p) p))]
             [posn? ((pred (λ (x) #t) p) -> (pred boolean? p))]
             [posn-x ((pred (posn? ^ p p) p) -> (pred exact-nonnegative-integer? p))]
             [posn-y ((pred (posn? ^ p p) p) -> (pred exact-nonnegative-integer? p))]))]))
 
 (test/v-->> (---> Ms)
             (term (↓ (@ (posn ^ † p) 1 2 †) (env)))
             (term (-- (struct posn
                         (-- (↓ 1 (env)))
                         (-- (↓ 2 (env))))
                       ((pred (posn? ^ p p) p) (env)))))
 (test/v-->> (---> Ms)
             (term (↓ (@ (posn? ^ † p)
                         (@ (posn ^ † p) 1 2 †)
                         †)
                      (env)))
             (term (-- (↓ #t (env)))))
 (test/v-->> (---> Ms)
             (term (↓ (@ (posn-x ^ † p)
                         (@ (posn ^ † p) 1 2 †)
                         †)
                      (env)))
             (term (-- (↓ 1 (env)))))
 (test/v-->> (---> Ms)
             (term (↓ (@ (posn-y ^ † p)
                         (@ (posn ^ † p) 1 2 †)
                         †)
                      (env)))
             (term (-- (↓ 2 (env))))))
