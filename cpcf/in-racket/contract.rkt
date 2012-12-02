#lang racket
(require racket/contract)
(require "env.rkt")
(require "lang.rkt")
(require "prim.rkt")
(require "nd.rkt")

(provide
 (contract-out
  [C⇒? (CC? CC? . -> . verified?)]
  [simplify-CC (CC? . -> . (set/c (set/c simpl-CC?)))]
  [refine ((set/c simpl-CC?) CC? . -> . (set/c (set/c simpl-CC?)))]
  [FC (symbol? con? . -> . (or/c #f (list/c exp?)))])
 simpl-CC?)

;; checks for simple closed contract
(define simpl-CC?
  (match-lambda
    [(CC (or [? FLAT/C?] [? FUNC/C?] [? STRUCT/C?]) (? env?)) #t]
    [_ #f]))

;; simplify contract into (possibilities-of (sets-of 'simpler'-contracts))
;; specifically: split or/c, unroll μ, look up reference, and break and/c
(define (simplify-CC C)
  (match-let ([(CC c ρ) C])
    (match c
      [(OR/C c1 c2) (non-det:
                     [s1 ← (simplify-CC (close c1 ρ))]
                     [s2 ← (simplify-CC (close c2 ρ))]
                     [return: s1 s2])]
      [(AND/C c1 c2) (non-det:
                      [s1 ← (simplify-CC (close c1 ρ))]
                      [s2 ← (simplify-CC (close c2 ρ))]
                      [return: (set-union s1 s2)])]
      [(MU/C x c′) (simplify-CC (close c′ (env+ ρ x (VO C '∅))))]
      [(REF/C x) (simplify-CC (VO-v (env-get ρ x)))]
      [_ (non-det: [return: {set C}])])))

;; checks whether first contract implies/precludes second
(define (C⇒? A B)
  (match-let ([(CC a ρA) A]
              [(CC b ρB) B])
    (match* (a b)
      ; trivial 'any/c' contract
      [(_ [FLAT/C (PRED 'tt)]) 'Proved]
      ; flat contract, can tell answer for primitive predicates
      [([FLAT/C (? pred? p)] [FLAT/C (? pred? q)]) (p⇒? p q)]
      ; break and/or contracts into simpler ones
      [((OR/C a1 a2) _) (∧ (C⇒? (close a1 ρA) B) (C⇒? (C⇒? a2 ρA) B))]
      [(_ (OR/C b1 b2)) (∨ (C⇒? A (close b1 ρB)) (C⇒? A (close b2 ρB)))]
      [((AND/C a1 a2) _) (∨ (C⇒? (close a1 ρA) B) (C⇒? (C⇒? a2 ρA) B))]
      [(_ (AND/C b1 b2)) (∧ (C⇒? A (close b1 ρB)) (C⇒? A (close b2 ρB)))]
      ; unroll recursive contract
      [((MU/C x a′) _) (C⇒? (close a′ (env+ ρA x (VO A '∅))) B)]
      [(_ (MU/C x b′)) (C⇒? A (close b′ (env+ ρB x (VO B '∅))))]
      ; look-up contract reference
      [((REF/C x) _) (C⇒? (VO-v (env-get ρA x)) B)]
      [(_ (REF/C x)) (C⇒? A (VO-v (env-get ρB x)))]
      ; struct/c
      [((STRUCT/C ta as) _)
       (match b
         [(STRUCT/C tb bs)
          (if (and [equal? ta tb] [= (length as) (length bs)])
              (apply ∧ (map (λ (ai bi) (C⇒? (close ai ρA) (close bi ρB))) as bs))
              'Refuted)]
         [(FLAT/C (STRUCT-P tb _)) (if (equal? ta tb) 'Proved 'Refuted)]
         [(FUNC/C _ _ _) 'Refuted]
         [_ 'Neither])]
      ; func/c ; TODO: more precise??
      [((? FUNC/C?) (FLAT/C (? pred? p))) (p⇒? p (PRED 'proc?))]
      [((FUNC/C c d v?) (FUNC/C c′ d′ v?))
       (if (= (length c) (length c′))
           (∧ (apply ∧ (map (match-lambda**
                             [(`(,_ ,ci) `(,_ ,ci′)) (C⇒? ci′ ci)])
                            c c′))
              (C⇒? d d′))
           (if v? 'Neither 'Refuted))]
      ; remain conservative for everything else
      [(_ _) 'Neither])))

;; flattens contract into predicate
(define (FC m c)
  (define (FC′ c) (FC m c))
  (match c
    [(FLAT/C e) (list e)]
    [(OR/C c1 c2)
     (match* ([FC′ c1] [FC′ c2])
       [([list e1] [list e2]) (list (LAM '(x) (OR m e1 e2) #f))]
       [(_ _) #f])]
    [(AND/C c1 c2)
     (match* ([FC′ c1] [FC′ c2])
       [([list e1] [list e2]) (list (LAM '(x) (AND e1 e2) #f))]
       [(_ _) #f])]
    [(? FUNC/C?) #f]
    [(STRUCT/C t cs)
     (match (map FC′ cs)
       [`(,(list e) ...)
        (let ([n (length cs)])
          (list
           (LAM '(x)
                (apply AND ; label doesn't matter here. Should never blame!!
                       (cons [AP (STRUCT-P t n) (list 'x) '☠]
                             [map (λ (p i)
                                    (AP p
                                        (list [AP (STRUCT-AC t n i) (list 'x) '☠])
                                        m))
                                  e
                                  (build-list n identity)]))
                #f)))]
       [#f #f])]
    [(MU/C x c) (match (FC′ c)
                  [(list e) (list (MU x e))]
                  [#f #f])]
    [(REF/C x) (list x)]))

;; refines given set of contracts with new one
;; returns possibilities of refinements
(define (refine Cs new-C)
  (for/fold ([possibilities ∅]) ([new-Cs (simplify-CC new-C)])
    (match
        (for/fold ([possibility Cs]) ([Ci new-Cs])
          (match possibility
            ['Refuted 'Refuted]
            [_ (refine1 possibility Ci)]))
      ['Refuted possibilities]
      [p (set-add possibilities p)])))

;; refines given set of contracts with new (simple) one
(define (refine1 Cs C)
  (match
      ; check for possibilities:
      ; * current contracts are sufficient to deduce new one
      ; * current contracts preclude new one
      ; * new one is sufficient to replace old one
      ; * nothing is known, add new contract, might result in spurious stuff
      (for/fold ([acc 'Neither]) ([Ci Cs])
        (match acc
          ['Neither (match (C⇒? Ci C)
                      ['Neither (match (C⇒? C Ci)
                                  ['Proved `(Replace ,Ci)]
                                  ['Refuted 'Refuted]
                                  ['Neither 'Neither])]
                      ['Proved 'Redundant]
                      ['Refuted 'Refuted])]
          [(or 'Refuted 'Redundant `[Replace ,_]) acc]))
    ['Redundant Cs]
    ['Refuted 'Refuted]
    [`(Replace ,Ci) (set-add (set-remove Cs Ci) C)]
    ['Neither (set-add Cs C)]))