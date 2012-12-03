#lang racket
(require "lang.rkt")
(require "env.rkt")
(require "nd.rkt")

(provide
 (contract-out
  [∆ (symbol? symbol? . -> . exp?)]
  [p⇒? (pred? pred? . -> . verified?)]
  [C⇒? (CC? CC? . -> . verified?)]
  [simplify-CC (CC? . -> . (set/c (set/c simpl-CC?)))]
  [refine ((set/c simpl-CC?) CC? . -> . (set/c (set/c simpl-CC?)))]
  [refine* ([listof (set/c simpl-CC?)] [listof CC?] . -> . (set/c [listof (set/c simpl-CC?)]))]
  [refine-v (val? CC? . -> . (set/c val?))]
  [refine-V (V? CC? . -> . (set/c V?))]
  [refine-V* ([listof V?] [listof CC?] . -> . (set/c [listof V?]))]
  [split-struct
   (V? symbol? integer? . -> . (set/c (or/c 'Refuted [listof V?])))]
  [split-struct-C
   ([set/c simpl-CC?] symbol? integer? . -> .
                      (or/c 'Refuted 'Neither (set/c [listof (set/c simpl-CC?)])))]
  [FC (symbol? con? . -> . (or/c #f (list/c exp?)))])
 simpl-CC? pred? C/ANY C/NUM C/REAL C/STR)

;; common basic contracts
(define C/ANY (FLAT/C 'tt))
(define C/NUM (FLAT/C 'num?))
(define C/REAL (FLAT/C 'real?))
(define C/STR (FLAT/C 'str?))

(define c:
  (letrec
      ([mk-c
        (match-lambda
          [`(∧ ,c1 ,c2) (AND/C (mk-c c1) (mk-c c2))]
          [`(∨ ,c1 ,c2) (OR/C (mk-c c1) (mk-c c2))]
          [p? (FLAT/C p?)])])
    (match-lambda
      [`(,c1 → ,c) (FUNC/C `([x ,(mk-c c1)]) (mk-c c) #f)]
      [`(,c1 ,c2 → ,c) (FUNC/C `([x ,(mk-c c1)] [y ,(mk-c c2)]) (mk-c c) #f)])))

;; δ : Symbol [Listof [List V Path]] Γ -> [List Val Γ Path]
(define δ
  (match-lambda**
   
   ; +
   [('+ `(,(CLO (? number? x) _) ,(CLO (? number? y) _)) Γ)
    {set (CLO (+ x y) ρ0)}]))

;; ∆ : Symbol -> CON
(define ∆c
  (hash
   ;; operators
   '+ (c: '[num? num? → num?])
   '- (c: '[num? num? → num?])
   '* (c: '[num? num? → num?])
   '/ (c: '[(∧ num? non-zero?) num? → num?])
   
   ))

(define ∆preds
  (hash
   'tt #f
   'true? #f
   'false? #f
   'bool? #f
   'str? #f
   'proc? #f
   'cons? #f
   'num? #f
   'real? #f
   'int? #f
   'zero? (c: '[num? → tt])
   'non-zero? (c: '[num? → tt])))

(define (∆ caller x)
  (cond
    [(hash-has-key? ∆c x) (MON '∆ '∆ caller (hash-ref ∆c x) (PRIM x))]
    [(hash-has-key? ∆preds x)
     (match (hash-ref ∆preds x)
       [#f (PRED x)]
       [c (MON '∆ '∆ caller c (PRED x))])]
    [else (error "Unknown primitive identifier:" x)]))

;; primitive, type-like predicates
(define (pred? x)
  (or (PRED? x)
      (STRUCT-P? x)))

;; checks whether first predicate implies/precludes second
(define p⇒?
  (match-lambda**
   [(_ [PRED 'tt]) 'Proved]
   [(p p) 'Proved]
   [([PRED 'false?] [PRED 'true?]) 'Refuted]
   [(_ [PRED 'true?]) 'Proved]
   [([PRED (or 'zero? 'non-zero? 'int? 'real?)] [PRED 'num?]) 'Proved]
   [([PRED 'zero?] [PRED 'int?]) 'Proved]
   [([PRED (or 'zero? 'non-zero? 'int?)] [PRED 'real?]) 'Proved]
   [([PRED x] [PRED y])
    (if (ormap (λ (group)
                 (and (member x group) (member y group)))
               '({true? false?}
                 {false? proc? str? num?}
                 {false? proc? str? real?}
                 {false? proc? str? int?}))
        'Refuted
        'Neither)]
   
   [(_ _) 'Neither]))

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

;; refines given vector of contract sets with new vector of contracts
;; returns all possibilities
(define (refine* Cs* C*)
  (match* (Cs* C*)
    [('() _) {set '()}]
    [([cons Cs Cs1*] [cons C C1*])
     (non-det: [Cs′ ← (refine Cs C)]
               [Cs1*′ ← (refine* Cs1* C1*)]
               [return: (cons Cs′ Cs1*′)])]))

;; refines given vector of closed values with new vector of contracts
(define (refine-V* V* C*)
  (match* (V* C*)
    [('() _) {set '()}]
    [([cons V V1*] [cons C C1*])
     (non-det: [V′ ← (refine-V V C)]
               [V1*′ ← (refine-V* V1* C1*)]
               [return: (cons V′ V1*′)])]))

;; refines given set of contracts with new (simple) one
;; [Setof SimplCC] SimplCC -> [Setof SimplCC] or 'Refuted
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
    ['Neither (match C
                [(CC (FLAT/C (PRED 'tt)) _) Cs]
                [_ (set-add Cs C)])]))

;; attempts to split value into diffent struct fields
(define (split-struct V tag field-count)
  (match V
    [(C-STRUCT t fields) {set (if (equal? t tag) fields 'Refuted)}]
    [(CLO (OPQ refinements) _)
     (match (split-struct-C refinements tag field-count)
       ['Refuted {set 'Refuted}]
       ['Neither {set 'Refuted (make-list field-count [CLO • env0])}]
       [possibilities (s-map (curry map (λ (Cs) (CLO (OPQ Cs) env0)))
                             possibilities)])]
    [_ {set 'Refuted}]))

;; attempts to split a refinment set into refinements for each field
(define (split-struct-C refinements tag field-count)
  (for/fold ([acc 'Neither]) ([Ci refinements])
    (match acc
      ['Refuted 'Refuted]
      [_ (match Ci
           [(CC (STRUCT/C t cs) ρ)
            (if (and [equal? t tag] [= field-count (length cs)])
                (non-det (λ (Cs*) (refine* Cs* (map (λ (c) (close c ρ)) cs)))
                         (match acc
                           ['Neither {set (make-list field-count ∅)}]
                           [_ acc]))
                'Refuted)]
           [(CC (FLAT/C p) _)
            (match p
              [(? pred?) (match (p⇒? p (STRUCT-P tag field-count))
                           ['Proved {set (make-list field-count ∅)}]
                           [x x])]
              [_ 'Neither])]
           [(CC (? FUNC/C?) _) 'Refuted])])))

(define (refine-v v CC)
  (match v
    [(OPQ refinements) (s-map
                        (λ (CC1) (OPQ CC1))
                        (refine refinements CC))]
    [_ {set v}]))

(define (refine-V V CC)
  (match V
    [(CLO v ρ) (s-map
                (λ (v1) (CLO v1 ρ))
                (refine-v v CC))]
    [_ {set V}])) ; TODO: eliminate spurious stuff