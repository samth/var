#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt" "subst.rkt" "meta-misc.rkt")
(provide (except-out (all-defined-out) test))
(provide (all-from-out "meta-misc.rkt"))
(test-suite test meta)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metafunctions

(define-metafunction λc~
  demonic* : C V -> E
  [(demonic* C CV)
   (@ (demonic C) CV ★)]
  [(demonic* C blessed-AV)
   (@ (demonic C) blessed-AV ★)]
  [(demonic* C blessed-A)
   (@ (demonic C) blessed-A ★)]
  [(demonic* C AV) ;; produces trivial expression
   (-- 0)])

(define-metafunction λc~
  amb : E E ... -> E
  [(amb E) E]
  [(amb E_1 E_2 ...) (if (-- (any/c)) E_1 (amb E_2 ...))])

;; Produce a function that will do "everything" it can
;; to its argument while treating it as a C.
;; The only important part is that functions are applied
;; to all possible values.  Note that this requires traversing
;; pairs.
(define-metafunction λc~
  demonic : C -> L
  [(demonic FC) (λ (x) #t)]
  [(demonic (pred SV ℓ)) ;; MAYBE improve me: special case o?
   (λ f (x) (if (@ proc? x ★) 
                (@ f (@ x (-- (any/c)) ★) ★)  ;; want to add fact that x is a proc.
                (if (@ cons? x ★)
                    (amb (@ f (@ first x ★) ★)
                         (@ f (@ rest x ★) ★))
                    #t)))]  
  
  [(demonic (and/c C_0 C_1))
   (λ (x) (begin (@ (demonic C_0) x ★)
                 (@ (demonic C_1) x ★)))]
  
  [(demonic (cons/c C_0 C_1))
   (λ (x) (begin (@ (demonic C_0) (@ first x ★) ★)
                 (@ (demonic C_1) (@ rest x ★) ★)))]
  
  [(demonic (or/c C_0 C_1))
   (demonic (any/c))]  ;; Always safe, hard to do better.
   
  [(demonic (rec/c x C))
   (demonic (any/c))]  ;; Safe.  What else could you do?
  
  [(demonic (C_0 ... -> C_1)) 
   (λ (f) (@ (demonic C_1) (@ f (-- C_0) ... ★) ★))
   (where f ,(gensym 'f))]
  [(demonic (C_0 ... -> (λ (x ...) C_1))) 
   (λ (f) (@ (demonic (subst/C ((x (-- C_0)) ...) C_1)) (@ f (-- C_0) ... ★) ★))
   (where f ,(gensym 'f))])

;; Does o? hold on all values abstracted by V
;; [Gives an approximate answer: #f means "failed to prove"]
(define-metafunction λc~
  proves : V o? -> #t or #f
  [(proves (-- PV C ...) o?)
   #t
   (where #t (plain-δ o? PV Λ))]
  [(proves (-- C_0 ... C C_1 ...) o?) 
   #t
   (where #t (proves-con C o?))]
  [(proves ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 V) o?)
   (proves V o?)]
  [(proves V o?) #f])

(test
 (test-equal (term (proves (-- "Hi") string?)) #t)
 (test-equal (term (proves ((--> (any/c)) <= f g (-- 0) h (-- (pred proc? Λ))) proc?)) #t))

;; Does (negate o?) hold on all values abstracted by AV
(define-metafunction λc~
  refutes : V o? -> #t or #f
  [(refutes (-- C_0 ... C C_1 ...) o?) 
   #t
   (where #t (refutes-con C o?))]
  [(refutes (-- PV C ...) o?)
   #t
   (where #f (plain-δ o? PV Λ))]
  [(refutes ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 any_1) o?)
   #t
   (side-condition (not (eq? 'proc? (term o?))))]
  [(refutes ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 V) o?)
   (refutes V o?)]
  [(refutes V o?) #f])

(test
 (test-equal (term (refutes (-- 0) empty?)) #t)
 (test-equal (term (refutes (-- (cons/c (pred nat? p) (pred nat? p))) cons?)) #f)
 (test-equal (term (refutes ((--> (any/c)) <= f g (-- 0) h (-- (pred nat? Λ))) proc?)) #t))

;; Does satisfying C imply o?
(define-metafunction λc~
  proves-con : C o? -> #t or #f
  [(proves-con (pred o?_0 ℓ) o?_1) 
   (proves-predicate o?_0 o?_1)]
  [(proves-con (or/c C_0 C_1) o?)
   ,(and (term (proves-con C_0 o?))
         (term (proves-con C_1 o?)))]
  [(proves-con (and/c C_0 C_1) o?)
   ,(or (term (proves-con C_0 o?))
        (term (proves-con C_1 o?)))]
  [(proves-con (cons/c C_0 C_1) cons?) #t]
  [(proves-con (C_0 ... -> any) proc?) #t]
  [(proves-con C o?) #f])

(define-metafunction λc~
  proves-predicate : o? o? -> #t or #f
  [(proves-predicate o? o?) #t]
  [(proves-predicate zero? nat?) #t]
  [(proves-predicate false? bool?) #t]
  [(proves-predicate o?_0 o?_1) #f])

;; Does satisfying C imply (negate o?)
(define-metafunction λc~
  refutes-con : C o? -> #t or #f
  [(refutes-con (C_0 ... -> any) proc?) #f]
  [(refutes-con (C_0 ... -> any) o?) #t]
  [(refutes-con (pred o?_0 ℓ) o?_1) 
   (refutes-predicate o?_0 o?_1)]
  [(refutes-con (or/c C_0 C_1) o?)
   ,(and (term (refutes-con C_0 o?))
         (term (refutes-con C_1 o?)))]
  [(refutes-con (and/c C_0 C_1) o?)
   ,(or (term (refutes-con C_0 o?))
        (term (refutes-con C_1 o?)))]
  [(refutes-con (cons/c C_0 C_1) o?) 
   #t
   (side-condition (not (eq? (term o?) 'cons?)))]
  [(refutes-con (rec/c x C) o?) 
   (refutes-con (unroll (rec/c x C)) o?)   ;; Productive implies you'll never get
   (where #t (productive? (rec/c x C)))]   ;; back to (rec/c x C) in this metafunction.
  [(refutes-con C o?) #f])

(define-metafunction λc~
  refutes-predicate : o? o? -> #t or #f
  [(refutes-predicate o? o?) #f]
  [(refutes-predicate empty? o?) #t]
  [(refutes-predicate cons? o?) #t]
  [(refutes-predicate nat? zero?) #f]
  [(refutes-predicate zero? nat?) #f]
  [(refutes-predicate nat? o?) #t]
  [(refutes-predicate zero? o?) #t]
  [(refutes-predicate proc? o?) #t]
  [(refutes-predicate bool? false?) #f]
  [(refutes-predicate bool? o?) #t]
  [(refutes-predicate string? o?) #t]
  [(refutes-predicate false? bool?) #f]
  [(refutes-predicate false? o?) #t])
  

;; Totality tests
(test
 (redex-check λc~ (AV o?)
              (boolean? (term (proves AV o?))))
 (redex-check λc~ (AV o?)
              (boolean? (term (refutes AV o?))))
 (redex-check λc~ (C o?)
              (boolean? (term (proves-con C o?))))
 (redex-check λc~ (C_1 o?) ;; maybe restrict C_1 to valid?
              (boolean? (term (refutes-con C_1 o?)))))

  
;; Note: (proves-con C o?) and (refutes-con C o?) *both* hold
;; when C is inconsistent, e.g. (and/c nat? cons?).

(test
 (test-equal (term (proves-con (pred empty? ℓ) empty?)) #t)
 (test-equal (term (proves-con (pred cons? ℓ) empty?)) #f)
 (test-equal (term (proves-con (or/c (pred empty? ℓ)
                                     (pred cons? ℓ))
                               empty?))
             #f)
 (test-equal (term (proves-con (and/c (pred empty? ℓ)
                                      (pred cons? ℓ))
                               empty?))
             #t)
 (test-equal (term (proves-con ((pred empty? ℓ) -> (pred cons? ℓ))
                               empty?))
             #f)
 
 (test-equal (term (refutes-con (pred empty? ℓ) empty?)) #f)
 (test-equal (term (refutes-con (pred cons? ℓ) empty?)) #t)
 (test-equal (term (refutes-con (and/c (pred empty? ℓ)
                                       (pred cons? ℓ))
                                empty?))
             #t)) 
  
;; Does this value definitely pass this contract?
(define-metafunction λc~
  contract-in : C V -> #t or #f
  [(contract-in C (-- PV C_0 ... C C_1 ...)) #t]
  [(contract-in C (-- C_0 ... C C_1 ...)) #t]
  [(contract-in C ((C_0 ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 V))
   (contract-in C V)]
  [(contract-in (pred (f ^ ℓ_0) ℓ_2) 
                (-- PV C_0 ... (pred (f ^ ℓ_1) ℓ_3) C_1 ...)) 
   #t]
  [(contract-in (pred (f ^ ℓ_0) ℓ_2) 
                (-- C_0 ... (pred (f ^ ℓ_1) ℓ_3) C_1 ...)) 
   #t]
  [(contract-in (pred o? ℓ) V)
   (proves V o?)]
  [(contract-in (and/c C_1 C_2) V)
   ,(and (term (contract-in C_1 V)) (term (contract-in C_2 V)))]
  [(contract-in (or/c C_1 C_2) V)
   ,(or (term (contract-in C_1 V)) (term (contract-in C_2 V)))]
  [(contract-in (cons/c C_1 C_2) (-- (cons V_1 V_2) C ...))
   ,(and (term (contract-in C_1 V_1)) (term (contract-in C_2 V_2)))]
  [(contract-in (cons/c C_1 C_2) AV)
   ,(and (andmap (λ (x) (term (contract-in C_1 ,x))) (term (proj-left AV)))
         (andmap (λ (x) (term (contract-in C_2 ,x))) (term (proj-right AV))))]
  [(contract-in C V) #f])

;; Does this abstract value *definitely* fail this contract?
(define-metafunction λc~
  contract-not-in : C V -> #t or #f  
  [(contract-not-in C V)
   (contract-not-in/cache C V ())])

(define-metafunction λc~
  contract-not-in/cache : C V ((C V) ...) -> #t or #f
  [(contract-not-in/cache C V ((C_0 V_0) ... (C V) (C_1 V_1) ...)) #f]
  [(contract-not-in/cache C ((C_0 ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 V) any)
   (contract-not-in/cache C V any)]
  [(contract-not-in/cache (pred o? ℓ) V any)
   (refutes V o?)]
  [(contract-not-in/cache (cons/c C_1 C_2) V ((C_3 V_3) ...))
   ,(or (term (refutes V cons?)) (term bool_cars) (term bool_cdrs))
   (where (V_car ...) ,(filter (redex-match λc~ V) (term (δ (@ first V Λ)))))
   (where (V_cdr ...) ,(filter (redex-match λc~ V) (term (δ (@ rest V Λ)))))
   (where bool_cars ,(andmap values (term ((contract-not-in/cache C_1 V_car (((cons/c C_1 C_2) V) (C_3 V_3) ...)) ...))))
   (where bool_cdrs ,(andmap values (term ((contract-not-in/cache C_2 V_cdr (((cons/c C_1 C_2) V) (C_3 V_3) ...)) ...))))
   ]
  [(contract-not-in/cache FC V any)
   #t
   (where #t (proves V proc?))]
  [(contract-not-in/cache (and/c C_1 C_2) V ((C_3 V_3) ...))
   ,(or (term (contract-not-in/cache C_1 V (((and/c C_1 C_2) V) (C_3 V_3) ...)))
        (term (contract-not-in/cache C_2 V (((and/c C_1 C_2) V) (C_3 V_3) ...))))]
  [(contract-not-in/cache (or/c C_1 C_2) V ((C_3 V_3) ...))
   ,(and (term (contract-not-in/cache C_1 V (((or/c C_1 C_2) V) (C_3 V_3) ...)))
         (term (contract-not-in/cache C_2 V (((or/c C_1 C_2) V) (C_3 V_3) ...))))]
  
  [(contract-not-in/cache (rec/c x C) V ((C_3 V_3) ...))
   (contract-not-in/cache (unroll (rec/c x C)) V (((rec/c x C) V) (C_3 V_3) ...))
   (where #t (productive? (rec/c x C)))]
                    
  
  [(contract-not-in/cache (C_1 ... -> any) V any_1)
   #t
   (where #t (refutes V proc?))]
  
  [(contract-not-in/cache C V any) #f])



(test
 ;; testing termination
 (term (contract-not-in (cons/c (pred nat? Λ) (rec/c X (or/c (pred empty? Λ) (cons/c (pred nat? Λ) X))))
                        (-- (cons/c (any/c) (rec/c Y (or/c (empty/c) (cons/c (any/c) Y)))))))
 (test-equal (term (contract-not-in (cons/c (any/c) (any/c))  (-- 0)))
             #t)
 (test-equal (term (contract-not-in (rec/c x (or/c (pred empty? Λ) (cons/c (pred nat? Λ) x))) (-- 0)))
             #t))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; δ

(define-metafunction λc~
  δ : (@ o V ... ℓ) -> (V-or-B V-or-B ...)
  [(δ (@ cons V_0 V_1 ℓ)) ((-- (cons V_0 V_1)))]  
  [(δ (@ proc? ((C ... --> any) <= ℓ_1 ℓ_2 V-or-AE ℓ_3 any_1) ℓ)) ((-- #t))]
  [(δ (@ o V_0 ... ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 V) V_1 ... ℓ))
   (δ (@ o V_0 ... V V_1 ... ℓ))]
  [(δ (@ o (-- PV C ...) ... ℓ)) (wrap (plain-δ o PV ... ℓ))]
  [(δ (@ o V ... ℓ)) (abstract-δ o V ... ℓ)])

(define-metafunction λc~
  wrap : any -> (V-or-B)
  [(wrap PV) [(-- PV)]]
  [(wrap B) [B]]
  [(wrap V) [V]])

(define-metafunction λc~
  plain-δ : o PV ... ℓ -> V or PV or B  
  [(plain-δ string? string ℓ) #t]
  [(plain-δ string? PV ℓ) #f]
  [(plain-δ bool? bool ℓ) #t]
  [(plain-δ bool? PV ℓ) #f]
  [(plain-δ zero? 0 ℓ) #t]
  [(plain-δ zero? nat ℓ) #f]
  [(plain-δ proc? L ℓ) #t]
  [(plain-δ proc? PV ℓ) #f]
  [(plain-δ empty? empty ℓ) #t]
  [(plain-δ empty? PV ℓ) #f]
  [(plain-δ cons? (cons V_0 V_1) ℓ) #t]
  [(plain-δ cons? PV ℓ) #f]
  [(plain-δ nat? nat ℓ) #t]
  [(plain-δ nat? PV ℓ) #f]
  [(plain-δ false? #f ℓ) #t]
  [(plain-δ false? PV ℓ) #f]
  [(plain-δ add1 nat ℓ) ,(add1 (term nat))]
  [(plain-δ sub1 0 ℓ) 0]
  [(plain-δ sub1 nat ℓ) ,(sub1 (term nat))]
  [(plain-δ first (cons V_0 V_1) ℓ) V_0]
  [(plain-δ rest (cons V_0 V_1) ℓ) V_1]  
  [(plain-δ + nat_0 nat_1 ℓ) ,(+ (term nat_0) (term nat_1))]
  [(plain-δ - nat_0 nat_1 ℓ) ,(max 0 (- (term nat_0) (term nat_1)))]
  [(plain-δ * nat_0 nat_1 ℓ) ,(* (term nat_0) (term nat_1))]
  [(plain-δ expt nat_0 nat_1 ℓ) ,(expt (term nat_0) (term nat_1))]
  [(plain-δ = nat_0 nat_1 ℓ) ,(= (term nat_0) (term nat_1))]
  [(plain-δ < nat_0 nat_1 ℓ) ,(< (term nat_0) (term nat_1))]
  [(plain-δ <= nat_0 nat_1 ℓ) ,(<= (term nat_0) (term nat_1))]
  [(plain-δ > nat_0 nat_1 ℓ) ,(> (term nat_0) (term nat_1))]
  [(plain-δ >= nat_0 nat_1 ℓ) ,(>= (term nat_0) (term nat_1))]
  ;[(plain-δ cons PV_0 PV_1 ℓ) (cons (-- PV_0) (-- PV_1))]
  [(plain-δ string=? string_0 string_1 ℓ) ,(string=? (term string_0) (term string_1))]
  [(plain-δ string<? string_0 string_1 ℓ) ,(string<? (term string_0) (term string_1))]
  [(plain-δ string>? string_0 string_1 ℓ) ,(string>? (term string_0) (term string_1))]
  [(plain-δ string<=? string_0 string_1 ℓ) ,(string<=? (term string_0) (term string_1))]
  [(plain-δ string>=? string_0 string_1 ℓ) ,(string>=? (term string_0) (term string_1))]
  [(plain-δ string-ci=? string_0 string_1 ℓ) ,(string-ci=? (term string_0) (term string_1))]
  [(plain-δ string-ci<? string_0 string_1 ℓ) ,(string-ci<? (term string_0) (term string_1))]
  [(plain-δ string-ci>? string_0 string_1 ℓ) ,(string-ci>? (term string_0) (term string_1))]
  [(plain-δ string-ci<=? string_0 string_1 ℓ) ,(string-ci<=? (term string_0) (term string_1))]
  [(plain-δ string-ci>=? string_0 string_1 ℓ) ,(string-ci>=? (term string_0) (term string_1))]
  [(plain-δ o PV PV_0 ... ℓ)       ;; catches domain errors
   (blame ℓ o (-- PV) λ (-- PV))]) ;; FIXME: Not right value

(define-metafunction λc~
  impossible? : V -> #t or #f
  [(impossible? (-- PV C ...)) #f]
  [(impossible? (-- C))
   (impossible-con? C)]
  [(impossible? ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 V))
   (impossible? V)]
  [(impossible? ((C ... --> any) <= ℓ_0 ℓ_1 V_b ℓ_2 (addr a))) ;; for CESK only
   #f]
  [(impossible? (-- C_0 C_1 C ...))
   ,(or (term (impossible? (-- C_0 C ...)))
        (term (impossible-con? C_1)))])

(define-metafunction λc~
  impossible-con? : C -> #t or #f
  [(impossible-con? C)   ;; Relies on theorem in lang:
   #t                    ;; WC! /\ FVC! = uninhabited
   (where WC! C)         ;; FIXME: Combine this with feasible
   (where FVC! C)]
  [(impossible-con? (or/c C_0 C_1))
   ,(and (term (impossible-con? C_0))
         (term (impossible-con? C_1)))]  
  [(impossible-con? (and/c C_0 C_1))
   ,(or (term (impossible-con? C_0))
        (term (impossible-con? C_1)))]
  [(impossible-con? (cons/c C_0 C_1))
   ,(or (term (impossible-con? C_0))
        (term (impossible-con? C_1)))]
  [(impossible-con? C) #f])

(define-metafunction λc~
  abstract-δ : o V ... ℓ -> (V-or-B V-or-B ...)
  [(abstract-δ o V_0 ... V V_1 ... ℓ)
   ((-- #f)) ;; V is impossible, so why not?
   (where #t (impossible? V))]
  
  ;; o?
  [(abstract-δ o? V ℓ) 
   ((-- #t) (-- #f))
   (where #t (proves V o?))
   (where #t (refutes V o?))]
  [(abstract-δ o? V ℓ) ((-- #t)) (where #t (proves V o?))]
  [(abstract-δ o? V ℓ) ((-- #f)) (where #t (refutes V o?))]
  [(abstract-δ o? V ℓ) 
   ((-- #t) (-- #f))]
  
  ;; nat->nat
  [(abstract-δ nat->nat V ℓ)
   ((-- (pred nat? Λ)))
   (where #t (proves V nat?))]
  [(abstract-δ nat->nat V ℓ)
   ((blame ℓ nat->nat V λ V))
   (where #t (refutes V nat?))]
  [(abstract-δ nat->nat V ℓ)
   ((-- (pred nat? Λ))
    (blame ℓ nat->nat V λ V))]
  
  ;; first
  [(abstract-δ first V ℓ)
   (proj-left V)
   (where #t (proves V cons?))]
  [(abstract-δ first V ℓ)
   ((blame ℓ first V λ V))
   (where #t (refutes V cons?))]
  [(abstract-δ first V ℓ)
   (V-or-B ... (blame ℓ first V λ V))
   (where (V-or-B ...) (proj-left V))]
  
  ;; rest
  [(abstract-δ rest V ℓ)
   (proj-right V)
   (where #t (proves V cons?))]
  [(abstract-δ rest V ℓ)
   ((blame ℓ rest V λ V) )
   (where #t (refutes V cons?))]
  [(abstract-δ rest V ℓ)
   (V-or-B ... (blame ℓ rest V λ V))
   (where (V-or-B ...) (proj-right V))]
  
  ;; nat*nat->nat
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((-- (nat/c)))
   (where #t (proves V_0 nat?))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((blame ℓ nat*nat->nat V_0 λ V_0))
   (where #t (refutes V_0 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((blame ℓ nat*nat->nat V_1 λ V_1))
   (where #t (refutes V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((-- (nat/c))
    (blame ℓ nat*nat->nat V_1 λ V_1))
   (where #t (proves V_0 nat?))]  
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((-- (nat/c))
    (blame ℓ nat*nat->nat V_0 λ V_0))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->nat V_0 V_1 ℓ)
   ((-- (nat/c))
    (blame ℓ nat*nat->nat V_0 λ V_0)
    (blame ℓ nat*nat->nat V_1 λ V_1))]
  
  ;; nat*nat->bool
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((-- #t) (-- #f))
   (where #t (proves V_0 nat?))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((blame ℓ nat*nat->bool V_0 λ V_0))
   (where #t (refutes V_0 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((blame ℓ nat*nat->bool V_1 λ V_1))
   (where #t (refutes V_1 nat?))]    
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ nat*nat->bool V_1 λ V_1))
   (where #t (proves V_0 nat?))]  
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ nat*nat->bool V_0 λ V_0))
   (where #t (proves V_1 nat?))]
  [(abstract-δ nat*nat->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ nat*nat->bool V_0 λ V_0)
    (blame ℓ nat*nat->bool V_1 λ V_1))]
  
  ;; string*string->bool
  [(abstract-δ string*string->bool V_0 V_1 ℓ)
   ((-- #t) (-- #f))
   (where #t (proves V_0 string?))
   (where #t (proves V_1 string?))]
  [(abstract-δ string*string->bool V_0 V_1 ℓ)
   ((blame ℓ string*string->bool V_0 λ V_0))
   (where #t (refutes V_0 string?))]
  [(abstract-δ string*string->bool V_0 V_1 ℓ)
   ((blame ℓ string*string->bool V_1 λ V_1))
   (where #t (refutes V_1 string?))]  
  [(abstract-δ string*string->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ string*string->bool V_1 λ V_1))
   (where #t (proves V_0 string?))]  
  [(abstract-δ string*string->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ string*string->bool V_0 λ V_0))
   (where #t (proves V_1 string?))]
  [(abstract-δ string*string->bool V_0 V_1 ℓ)
   ((-- #t) 
    (-- #f)
    (blame ℓ string*string->bool V_0 λ V_0)
    (blame ℓ string*string->bool V_1 λ V_1))])


;; Project an AV to the left
;; (proj-left (-- (cons/c nat? string?) (cons/c zero? string?)))
;; ≡ (-- nat? zero?)
(define-metafunction λc~
  proj-left : AV -> (V ...)
  [(proj-left (-- C_0 C ...))
   (proj-left/a ((-- (any/c))) C_0 C ...)])

(define-metafunction λc~
  proj-right : AV -> (V ...)
  [(proj-right (-- C_0 C ...))
   (proj-right/a ((-- (any/c))) C_0 C ...)])

(define-metafunction λc~
  proj-left/a : ((-- C ...) ...) C ... -> (V ...)
  [(proj-left/a (AV ...)) (AV ...)]  
  [(proj-left/a (AV ...) (cons/c C_0 C_1) C_2 ...)
   (proj-left/a (AV_R ...) C_2 ...)
   (where (AV_R ...) 
          ,(for*/list ([av (in-list (term (AV ...)))]
                       [cnew (in-list (term (explode C_0)))])
             (term (remember-contract ,av ,cnew))))]
  [(proj-left/a (AV ...) C_0 C_1 ...)
   (proj-left/a (AV ...) C_1 ...)])

(define-metafunction λc~
  proj-right/a : ((-- C ...) ...) C ... -> (V ...)
  [(proj-right/a (AV ...)) (AV ...)]  
  [(proj-right/a (AV ...) (cons/c C_0 C_1) C_2 ...)
   (proj-right/a (AV_R ...) C_2 ...)
   (where (AV_R ...) 
          ,(for*/list ([av (in-list (term (AV ...)))]
                       [cnew (in-list (term (explode C_1)))])
             (term (remember-contract ,av ,cnew))))]
  [(proj-right/a (AV ...) C_0 C_1 ...)
   (proj-right/a (AV ...) C_1 ...)])

(test  
 (test-equal (term (δ (@ cons ((--> (nat/c)) <= f g (-- 0) h (-- (λ () 0))) (-- 0) q)))
             (term ((-- (cons ((--> (nat/c)) <= f g (-- 0) h (-- (λ () 0))) (-- 0))))))
 
 (test-equal (term (δ (@ proc? (-- ((any/c) -> (any/c))) †)))
             (term ((-- #t))))
 
 (test-equal (term (δ (@ cons (-- 1) (-- 2) †)))
             (term ((-- (cons (-- 1) (-- 2))))))
 
 (test-equal (term (δ (@ proc? (-- (nat/c)) ★)))
             (term ((-- #f))))
 
 (test-equal (term (δ (@ rest (-- (cons/c (any/c) (any/c))) f))) 
             (term ((-- (any/c)))))
 (test-equal (term (δ (@ rest (-- (cons/c (any/c) (or/c (nat/c) (string/c)))) f)))
             (term ((-- (nat/c)) (-- (string/c)))))  
 
 (test-equal (term (proj-right (-- (cons/c (any/c) (or/c (nat/c) (string/c))))))
             (term ((-- (nat/c)) (-- (string/c)))))
 
 (test-equal (term (refutes (-- (nat/c)) proc?))
             #t)
             
 (test-equal (term (refutes-con (nat/c) proc?))
             #t)
 
 (redex-check λc~ WFV (term (∈ #f (δ (@ proc? WFV ℓ)))))
 
 (test-equal (term (proves (-- #t) bool?)) #t)
 
 ;; Test for δ totalness.
 (redex-check λc~ (o1 V) (or (not (term (valid-value? V)))
                             (term (δ (@ o1 V f)))))
 (redex-check λc~ (o2 V_1 V_2) (or (not (term (valid-value? V_1)))
                                   (not (term (valid-value? V_2)))
                                   (term (δ (@ o2 V_1 V_2 f))))))