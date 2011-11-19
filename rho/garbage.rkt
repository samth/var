#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "util.rkt")
(provide gc)
(test-suite test garbage)

(define-metafunction λcρ
  gc : (D σ) -> (D σ)
  [(gc (D σ))
   (D (restrict-sto σ (live-loc D)))
   (side-condition (not (current-direct?)))]
  [(gc (D σ)) (D σ)])  

(define-metafunction λcρ
  restrict-sto : σ any -> σ
  [(restrict-sto σ any)
   ,(for/hash ([(a v) (term σ)]
               #:when (set-member? (term any) a))
      (values a v))])

(define-metafunction λcρ
  live-loc-env : ρ -> any
  [(live-loc-env ρ) 
   ,(for/set ((a (in-hash-values (term ρ))))
             a)])
  
(define-metafunction λcρ
  live-loc : D -> (side-condition any_s (set? (term any_s)))
  [(live-loc (clos EXP ρ))
   (live-loc-env ρ)]
  [(live-loc V) (live-loc-val V)]
  [(live-loc MODREF) ,(set)]
  [(live-loc (@ D ... LAB))
   ,(foldl set-union (set) (term ((live-loc D) ...)))]
  [(live-loc (@* D ... LAB))
   ,(foldl set-union (set) (term ((live-loc D) ...)))]
  [(live-loc (if D ...))
   ,(foldl set-union (set) (term ((live-loc D) ...)))]
  [(live-loc (let ((X D) ...) D_1))
   ,(foldl set-union (set) (term ((live-loc D_1) (live-loc D) ...)))]
  [(live-loc (begin D ...))
   ,(foldl set-union (set) (term ((live-loc D) ...)))]
  [(live-loc (CON ρ <= LAB_1 LAB_2 V LAB_3 D))
   ,(set-union (term (live-loc-env ρ))
               (term (live-loc V))
               (term (live-loc D)))]
  [(live-loc BLAME) (live-loc-blame BLAME)]
  [(live-loc (dem CON D))
   (live-loc D)])
  
(define-metafunction λcρ
  live-loc-blame : BLAME -> any
  [(live-loc-blame (blame LAB_1 LAB_2 V_1 (CON ρ) V_2)) 
   ,(set-union (term (live-loc V_1))
               (term (live-loc V_2))
               (term (live-loc-env ρ)))]
  [(live-loc-blame (blame LAB_1 LAB_2 V_1 PRIM V_2))
   ,(set-union (term (live-loc V_1))
               (term (live-loc V_2)))]   
  [(live-loc-blame (blame LAB_1 LAB_2 V_1 λ V_2))
   ,(set-union (term (live-loc V_1))
               (term (live-loc V_2)))])

(define-metafunction λcρ
  live-loc-con : C -> any
  [(live-loc-con (CON ρ)) (live-loc-env ρ)])

(define-metafunction λcρ
  live-loc-val : V -> any
  [(live-loc-val (-- (clos VAL ρ) C ...))
   ,(apply set-union 
           (term (live-loc-env ρ))
           (term ((live-loc-con C) ...)))]
  [(live-loc-val (-- (cons V_1 V_2) C ...))
   ,(apply set-union
           (term (live-loc-val V_1))
           (term (live-loc-val V_2))
           (term ((live-loc-con C) ...)))]
  [(live-loc-val (-- (struct X_1 X_2 V ...) C ...))
   ,(set-union (apply set-union (term ((live-loc-val V) ...)))
               (apply set-union (term ((live-loc-val C) ...))))]
  [(live-loc-val BLESSED) (live-loc-blessed BLESSED)]
  [(live-loc-val (-- C ...))
   ,(apply set-union (term ((live-loc-con C) ...)))])

(define-metafunction λcρ
  live-loc-blessed : BLESSED -> any
  [(live-loc-blessed (BARROW ρ <= LAB LAB V LAB BLESSED))
   ,(set-union (term (live-loc-env ρ))
               (term (live-loc-val V))
               (term (live-loc-blessed BLESSED)))]   
  [(live-loc-blessed (BARROW ρ <= LAB_1 LAB_2 V LAB_3 PROC))
   ,(set-union (term (live-loc-env ρ))
               (term (live-loc-val V))
               (term (live-loc-val PROC)))])
    

(test
 (test-equal (term (live-loc (clos x #hash((x . 3))))) (set 3)))
 


#|
(D (clos EXP ρ)     
     V
     MODREF 
     (@ D D ... LAB)     
     (@* D D ... LAB) ; like @, but last arg is a rest list [created by ->* checks].
     (if D D D)
     (let ((X D) ...) (clos EXP ρ))
     (begin D (clos EXP ρ))
     (CON ρ <= LAB LAB V LAB D)
     BLAME
     (dem CON D))
|#



