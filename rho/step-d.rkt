#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "meta-misc.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test demonic)

(define d
  (reduction-relation λcρ
   #:domain (D σ)
   (--> ((dem (and/c CON_1 ... CON CON_2 ...) V) σ)
        ((dem CON V) σ)
        dem-and)
   
   (--> ((dem (or/c CON_1 ... CON CON_2 ...) V) σ)
        ((dem CON V) σ)
        dem-or)
   
   (--> ((dem (rec/c X CON) V) σ)
        ((dem CON V) σ)
        dem-rec)
   (--> ((dem X V) σ)  ; safe, hard to do better.
        ((dem (∧) V) σ) 
        dem-var)
   
   (--> ((dem (not CON) V) σ) ; safe, hard to do better.
        ((dem (∧) V) σ)
        dem-not)
   
   (--> ((dem (cons/c CON_1 ..._1 CON CON_2 ..._2) 
              (-- (cons V_1 ..._1 V V_2 ..._2) C ...))
         σ)
        ((dem CON V) σ)
        dem-cons)
   
   (--> ((dem (struct/c X_m X_tag CON_1 ..._1 CON CON_2 ..._2)
              (-- (struct X_m X_tag V_1 ..._1 V V_2 ...) C ...))
         σ)
        ((dem CON V) σ)
        dem-struct)
   
   (--> ((dem (pred PREDV LAB) PROC) σ)
        ((dem (pred PREDV LAB) (@ PROC (-- ((∧) (env))) ★)) σ) ;; FIXME: arity
        dem-any-proc)
   (--> ((dem (pred PREDV LAB)  (-- (cons V_1 ... V V_2 ...) C ...)) σ)
        ((dem (pred PREDV LAB) V) σ)
        dem-any-cons)
   (--> ((dem (pred PREDV LAB) (-- (struct X_m X_tag V_1 ... V V_2 ...) C ...)) σ)
        ((dem (pred PREDV LAB) V) σ)
        dem-any-struct)
   
   (--> ((dem (CON_0 ... -> any) PROC) σ)
        ;; I worry about the (env) here -- can PROC do something that
        ;; cause preds in CON_0 to run?  If so, this is hosed.
        ((dem (CON_0 ... -> any) (@ PROC (-- (CON_0 (env))) ... ★)) σ)
        dem-arrow)))
