#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide m)
(test-suite test step-m)

(define (m Ms)
  (reduction-relation
   λcρ #:domain D
   (--> (X_1 ^ X X)
        (-- (clos VAL ()))
        (where VAL (lookup-modref/val X X_1 ,Ms))
        m-self)
   (--> (X_1 ^ LAB X)
        (CON () <= X LAB V X_1 V)
        (where CON (lookup-modref/con X X_1 ,Ms))
        (where VAL (lookup-modref/val X X_1 ,Ms))
        (where V (-- (clos VAL ())))
        (side-condition (not (eq? (term X) (term LAB))))
        m-other)))
    
(test 
 (define Ms 
   (term [(module m racket 
            (require) 
            (struct posn (x y))
            (define f 1)
            (provide/contract 
             [f (pred string? m)]
             [posn? ((pred (λ (x) #t) m) -> (pred boolean? m))]
             [posn ((pred exact-nonnegative-integer? m)
                    (pred exact-nonnegative-integer? m)
                    -> (pred (posn? ^ m m) m))]
             [posn-x ((pred (posn? ^ m m) m) -> (pred exact-nonnegative-integer? m))]
             [posn-y ((pred (posn? ^ m m) m) -> (pred exact-nonnegative-integer? m))]))]))
 (test--> (m Ms)
          (term (f ^ m m))
          (term (-- (clos 1 ()))))
 (test--> (m Ms)
          (term (f ^ † m))
          (term ((pred string? m) () <= m † (-- (clos 1 ())) f (-- (clos 1 ())))))
 (test--> (m Ms)
          (term (posn ^ m m))
          (term (-- (clos (s-cons posn 2) ()))))
 (test--> (m Ms)
          (term (posn? ^ m m))
          (term (-- (clos (s-pred posn) ()))))
 (test--> (m Ms)
          (term (posn-x ^ m m))
          (term (-- (clos (s-ref posn 0) ()))))
 (test--> (m Ms)
          (term (posn-y ^ m m))
          (term (-- (clos (s-ref posn 1) ())))))



;; modulename x valuename x modules -> value
(define-metafunction λcρ
  lookup-modref/val : X X (MOD ...) -> VAL or •
  [(lookup-modref/val X X_1 (MOD ... 
                             (module X LANG REQ STRUCT ... DEF ... (define X_1 any_result) DEF_1 ... 
                               any_p) ;; FIXME should make sure it's provided.
                             MOD_1 ...))
   any_result]
  [(lookup-modref/val X X_1 (MOD ...))
   OP
   (where OP (struct-cons? X X_1 (struct-env (MOD ...))))]
  [(lookup-modref/val X X_1 (MOD ...))
   OP
   (where OP (struct-ref? X X_1 (struct-env (MOD ...))))]
  [(lookup-modref/val X X_1 (MOD ...))
   OP
   (where OP (struct-pred? X X_1 (struct-env (MOD ...))))]
  [(lookup-modref/val X X_1 any)
   ,(format "unbound module variable ~a from ~a" (term X_1) (term X))])
          
;; modulename x valuename x modules -> contract
(define-metafunction λc-user
  lookup-modref/con : X X (MOD ...) -> CON
  [(lookup-modref/con X X_1 (MOD ... 
                             (module X LANG REQ STRUCT ... DEF ... 
                               (provide/contract any_1 ... [X_1 CON] any_2 ...))
                             MOD_1 ...))
   CON] 
  [(lookup-modref/con X X_1 any)
   (pred (λ (x) ,(format "contract for unbound module variable ~a from ~a" (term X_1) (term X))) ★)])
   
(test
 (define Ms 
   (term [(module m racket (require) (define f 1) (provide/contract [f (pred string? m)]))]))
 (test-equal (term (lookup-modref/val m f ,Ms)) 1)
 (test-equal (term (lookup-modref/val m g ,Ms)) "unbound module variable g from m")
 (test-equal (term (lookup-modref/con m f ,Ms)) (term (pred string? m)))
 (test-equal (term (lookup-modref/con m g ,Ms)) 
             (term (pred (λ (x) "contract for unbound module variable g from m") ★))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; structure definitions

(define-metafunction λcρ
  struct-cons? : X X STRUCTENV -> OP or #f
  [(struct-cons? X_def X_cons (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc ...)) any_3 ...) any_1 ...))
   (s-cons X_tag ,(length (term (X_acc ...))))]
  [(struct-cons? X_def X STRUCTENV) #f])

(define-metafunction λcρ
  struct-ref? : X X STRUCTENV -> OP or #f
  [(struct-ref? X_def X_acc (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X ... X_acc X_1 ...)) any_3 ...) any_1 ...))
   (s-ref X_tag ,(length (term (X ...))))]
  [(struct-ref? X_def X STRUCTENV) #f])

(define-metafunction λcρ
  struct-pred? : X X STRUCTENV -> OP or #f
  [(struct-pred? X_def X_pred (any_0 ... (X_def any_2 ... (X_tag X_cons X_pred (X_acc ...)) any_3 ...) any_1 ...))
   (s-pred X_tag)]
  [(struct-pred? X X_def STRUCTENV) #f])

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
