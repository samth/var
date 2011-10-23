#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide s)
(test-suite test step-s)

(define (s Ms)
  (redex-let 
   λcρ ([STRUCTENV (term (struct-env ,Ms))])
   (reduction-relation
    λcρ #:domain D
    (--> (@ (X_cons ^ LAB_use X_def) V ..._1 LAB)
         (-- (struct X_tag V ...))
         (where (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc ..._1)) any_3 ...) any_1 ...)
                STRUCTENV))    
    (--> (@ (X_pred ^ LAB_use X_def) (-- (struct X_tag V_1 ...) C ...) LAB)
         (-- (clos any_result ()))
         (where (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred* (X_acc ...)) any_3 ...) any_1 ...)
                STRUCTENV)
         ;; ensures f_pred is a predicate
         (where (any_0 ... (X_def any_2* ... (X_tag* X_cons* X_pred (X_acc* ...)) any_3* ...) any_1 ...)
                STRUCTENV)
         (where any_result ,(eq? (term X_tag) (term X_tag*))))    
    (--> (@ (X_pred ^ LAB_use X_def) V LAB)
         (-- (clos #f ()))
         (side-condition (not (redex-match λcρ STRUCTV (term V))))
         (where (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc ...)) any_3 ...) any_1 ...)
                STRUCTENV))
    (--> (@ (X_acc ^ LAB_use X_def) (-- (struct X_tag V_1 ...) C ...) LAB)
         V
         (where (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc* ...)) any_3 ...) any_1 ...)
                STRUCTENV)         
         (where ((X_acc1 ..._1 X_acc X_acc2 ..._2)
                 (V_2 ..._1 V V_3 ..._2))
                ((X_acc* ...)
                 (V_1 ...)))))))

(test
 (define Ms
   (term [(module f racket (require) 
            (struct posn (x y))
            (struct pair (x y))
            (provide/contract [posn (pred (λ (x) #t) Λ)]))]))
 (test--> (s Ms)
          (term (@ (posn ^ † f) (-- (clos 1 ())) (-- (clos 2 ())) †))
          (term (-- (struct posn (-- (clos 1 ())) (-- (clos 2 ()))))))
 (test--> (s Ms)
          (term (@ (posn? ^ † f) (-- (struct posn (-- (clos 1 ())) (-- (clos 2 ())))) †))
          (term (-- (clos #t ()))))
 (test--> (s Ms)
          (term (@ (posn? ^ † f) (-- (struct pair (-- (clos 1 ())) (-- (clos 2 ())))) †))
          (term (-- (clos #f ()))))
 (test--> (s Ms)
          (term (@ (posn? ^ † f) (-- (clos 3 ())) †))
          (term (-- (clos #f ()))))
 (test--> (s Ms)
          (term (@ (posn-x ^ † f) (-- (struct posn (-- (clos 1 ())) (-- (clos 2 ())))) †))
          (term (-- (clos 1 ()))))
 (test--> (s Ms)
          (term (@ (posn-y ^ † f) (-- (struct posn (-- (clos 1 ())) (-- (clos 2 ())))) †))
          (term (-- (clos 2 ())))))

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