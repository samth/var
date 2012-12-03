#lang racket
(require racket/contract)
(require "lang.rkt")
(require "env.rkt")
(require "prim.rkt")

(provide
 (contract-out
  [struct ¬ ([p pred?])]
  [Γ0 Γ?]
  [Γ+ (Γ? (or/c symbol? π?) ψ? . -> . Γ?)]
  [Γ-get (Γ? (or/c symbol? Π?) . -> . (set/c ψ?))]
  [Γ-mk ((or/c set? list? env?) Γ? . -> . Γ?)]
  [Γ-upd (Γ? Γ? . -> . Γ?)]
  [Γ-pop (Γ? (or/c symbol? [listof symbol?]) . -> . Γ?)]
  [Γ-push (Γ? (or/c symbol? [listof symbol?]) . -> . Γ?)]
  [ψ⇒? (ψ? ψ? . -> . verified?)]
  [¬p ((or/c pred? ¬?) . -> . ψ?)])
 Γ? ψ?)

(define Γ0 env0)

(struct ¬ (p) #:transparent)
(define (ψ? x)
  ((or/c pred? ¬?) x))
(define Γ? (hash/c symbol? (hash/c (listof STRUCT-AC?) (set/c ψ?))))

;; checks whether first ψ implies second
(define ψ⇒?
  (match-lambda**
   [(_ [PRED 'tt]) 'Proved]
   [(ψ ψ) 'Proved]
   [([PRED 'false?] [PRED 'true?]) 'Refuted]
   [(_ [PRED 'true?]) 'Proved]
   
   [([? PRED? p] [? PRED? q]) (p⇒? p q)]
   [([? PRED? p] [¬ q]) (v¬ (p⇒? p q))]
   [([¬ p] [¬ q]) (p⇒? q p)]
   
   [(_ _) 'Neither]))

;; negates + simplifies predicate
(define ¬p
  (match-lambda
    [(? pred? p) (¬ p)]
    [(¬ p) p]))

;; makes proposition environment with given domain
;; that knows everything Γ knows
(define (Γ-mk dom Γ)
  (define fresh-Γ
    (cond
      [(env? dom) (let ([Γ′ env0])
                    (hash-for-each dom
                                   (λ (x v) (set! Γ′ (hash-set Γ′ x env0))))
                    Γ′)]
      [else (for/fold ([Γ′ env0]) ([x dom])
              (hash-set Γ′ x env0))]))
  (Γ-upd fresh-Γ Γ))


;; updates Γ1 with all Γ2 knows
;; assume Γ2 knows no less than Γ1
(define (Γ-upd Γ1 Γ2)
  (if (< (env-size Γ1) (env-size Γ2))
      (hash-for-each Γ1 (λ (k _)
                          (when (hash-has-key? Γ2 k)
                            (set! Γ1 (hash-set Γ1 k (hash-ref Γ2 k))))))
      (hash-for-each Γ2 (λ (k v)
                          (when (hash-has-key? Γ1 k)
                            (set! Γ1 (hash-set Γ1 k v))))))
  Γ1)

;; removes symbol from environment's domain
(define Γ-pop env-pop)

;; reset values for symbol in environment
(define (Γ-push Γ x)
  (cond
    [(symbol? x) (hash-set Γ x env0)]
    [else (foldl (λ (z Γ1) (hash-set Γ1 z)) Γ x)]))

;; looks up path in environment
(define (Γ-get Γ o)
  (match o
    [(? symbol? x) (hash-ref (hash-ref Γ x) '() (λ () ∅))]
    [(Π accs x) (hash-ref (hash-ref Γ x) accs (λ () ∅))]))

;; updates path in environment
(define (Γ+ Γ o ψ)
  (match o
    ['∅ Γ]
    [(? symbol? x) (hash-update
                    Γ x
                    (λ (tb) (hash-update
                             tb '()
                             (λ (ψs) (set-add ψs ψ))
                             (λ () {set ψ}))))]
    [(Π accs x) (hash-update
                 Γ x
                 (λ (tb) (hash-update
                          tb accs
                          (λ (ψs) (set-add ψs ψ))
                          (λ () {set ψ}))))]))
