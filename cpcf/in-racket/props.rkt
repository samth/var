#lang racket
(require racket/contract)
(require "lang.rkt")
(require "prim.rkt")
(require "contract.rkt")

(provide
 (contract-out
  [struct ¬ ([p pred?])]
  [struct struct-ψ ([tag symbol?] [fields (listof ψ?)])]
  [struct Γ ([x↦π (hash/c symbol? (hash/c (listof STRUCT-AC?) ψ?))])]
  [Γ+ (Γ? π? ψ? . -> . Γ?)]
  [ψ⇒? (ψ? ψ? . -> . verified?)]
  [¬p ((or/c pred? ¬?) . -> . ψ?)])
 ψ?)

(struct ¬ (p) #:transparent)
(struct struct-ψ (tag fields) #:transparent)
(define (ψ? x)
  ((or/c pred? ¬? struct-ψ?) x))
         

(struct Γ (x↦π) #:transparent)

(define (Γ+ γ o ψ)
  (error "TODO"))

(define ψ⇒?
  (match-lambda**
   [(_ [PRED 'tt]) 'Proved]
   [(ψ ψ) 'Proved]
   [([PRED 'false?] [PRED 'true?]) 'Refuted]
   [(_ [PRED 'true?]) 'Proved]
   
   [([? PRED? p] [? PRED? q]) (p⇒? p q)]
   [([? PRED? p] [¬ q]) (v¬ (p⇒? p q))]
   [([¬ p] [¬ q]) (p⇒? q p)]
   
   [([struct-ψ t1 ψs1] [struct-ψ t2 ψs2]) (if (equal? t1 t2)
                                              (apply ∧ (map ψ⇒? ψs1 ψs2))
                                              'Refuted)]
   [([struct-ψ t ψs1] [STRUCT-P t _]) 'Proved]
   [([struct-ψ t ψs1] [? pred? p]) (if (p⇒? p (PRED 'proc?))
                                       'Refuted
                                       'Neither)]
   
   [(_ _) 'Neither]))

(define ¬p
  (match-lambda
    [(? pred? p) (¬ p)]
    [(¬ p) p]))
  