#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide #;s) ;; FIXME
(test-suite test step-s)

;; FIXME
#|
(define (s Ms)
  (redex-let 
   λcρ ([STRUCTENV (term (struct-env ,Ms))])
   (reduction-relation
    λcρ #:domain D
    (--> (@ (f_cons ^ ℓ_use f_def) V ..._1 ℓ)
         (-- (struct f_tag V ...))         
         (where (any_0 ... (f_def any_2 ... (f_tag f_cons f_pred (f_acc ..._1)) any_3 ...) any_1 ...)
                STRUCTENV))
    (--> (@ (f_pred ^ ℓ_use f_def) (-- (struct f_tag V_1 ...) C ...) ℓ)
         (-- PV)
         (where (any_0 ... (f_def any_2 ... (f_tag f_cons f_pred* (f_acc ...)) any_3 ...) any_1 ...)
                STRUCTENV)
         ;; ensures f_pred is a predicate
         (where (any_0 ... (f_def any_2* ... (f_tag* f_cons* f_pred (f_acc* ...)) any_3* ...) any_1 ...)
                STRUCTENV)
         (where PV ,(eq? (term f_tag) (term f_tag*))))    
    (--> (@ (f_pred ^ ℓ_use f_def) V ℓ)
         (-- #f)
         (side-condition (not (redex-match λcρ STRUCTV (term V))))
         (where (any_0 ... (f_def any_2 ... (f_tag f_cons f_pred (f_acc ...)) any_3 ...) any_1 ...)
                STRUCTENV))
    (--> (@ (f_acc ^ ℓ_use f_def) (-- (struct f_tag V_1 ...) C ...) ℓ)
         V
         (where (any_0 ... (f_def any_2 ... (f_tag f_cons f_pred (f_acc* ...)) any_3 ...) any_1 ...)
                STRUCTENV)         
         (where ((f_acc1 ..._1 f_acc f_acc2 ..._2)
                 (V_2 ..._1 V V_3 ..._2))
                ((f_acc* ...)
                 (V_1 ...)))))))

(test
 (define Ms
   (term [(module f racket (require) 
            (struct posn (x y))
            (struct pair (x y))
            (provide/contract [posn (any/c)]))]))   
 (test--> (s Ms)
          (term (@ (posn ^ † f) (-- 1) (-- 2) †))
          (term (-- (struct posn (-- 1) (-- 2)))))
 (test--> (s Ms)
          (term (@ (posn? ^ † f) (-- (struct posn (-- 1) (-- 2))) †))
          (term (-- #t)))
 (test--> (s Ms)
          (term (@ (posn? ^ † f) (-- (struct pair (-- 1) (-- 2))) †))
          (term (-- #f)))
 (test--> (s Ms)
          (term (@ (posn? ^ † f) (-- 3) †))
          (term (-- #f)))
 (test--> (s Ms)
          (term (@ (posn-x ^ † f) (-- (struct posn (-- 1) (-- 2))) †))
          (term (-- 1)))
 (test--> (s Ms)
          (term (@ (posn-y ^ † f) (-- (struct posn (-- 1) (-- 2))) †))
          (term (-- 2))))
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; structure definitions

(define-metafunction λcρ
  struct-env : (MOD ...) -> STRUCTENV
  [(struct-env ((module X_m LANG REQ STRUCT ... DEF ... PROV) ...))
   ((X_m (struct-names STRUCT) ...) ...)])
 
(define-metafunction λcρ
  struct-names : STRUCT -> (X X X (X ...))
  [(struct-names (struct X_tag (X_fld ...)))
   (X_tag (tag->cons X_tag) (tag->pred X_tag) ((fld->acc X_tag X_fld) ...))])

;; Change this if you want constructors and tags to be different.
(define-metafunction λcρ
  tag->cons : X -> X
  [(tag->cons X) X])
(define-metafunction λcρ
  tag->pred : X -> X
  [(tag->pred X) ,(string->symbol (format "~a?" (term X)))])
(define-metafunction λcρ
  fld->acc : X X -> X
  [(fld->acc X_tag X_fld) ,(string->symbol (format "~a-~a" (term X_tag) (term X_fld)))])
        
        
(test
 (test-equal (term (tag->cons posn)) (term posn))
 (test-equal (term (tag->pred posn)) (term posn?))
 (test-equal (term (fld->acc posn x)) (term posn-x))
 (test-equal (term (fld->acc posn y)) (term posn-y))
 
 (test-equal (term (struct-names (struct posn (x y))))                                 
             (term (posn posn posn? (posn-x posn-y))))
 
 (test-equal (term (struct-env [(module p racket
                                  (require)
                                  (struct posn (x y))
                                  (provide/contract))]))
             (term ((p (posn posn posn? (posn-x posn-y)))))))