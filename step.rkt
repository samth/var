#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "meta.rkt" "test.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relations

(define v
  (reduction-relation
   λc~ #:domain E
   (--> PV (-- PV) wrap)
   (--> ((-- (λ x E) C ...) V f) 
        (subst x V E) 
        β)
   (--> ((-- (λ x_0 x_1 E) C ...) V f) 
        (subst x_0 (-- (λ x_0 x_1 E) C ...) (subst x_1 V E)) 
        β-rec)   
   (--> (WFV V f) (blame f Λ WFV λ WFV) wrong)
   
   (--> (if V E_1 E_2) E_1
        (where (-- PV C ...) V)
        (side-condition (term PV))
        if-t)
   (--> (if V E_1 E_2) E_2 
        (where (-- PV C ...) V)
        (side-condition (not (term PV)))
        if-f)   
   (--> (o V ... f)
        (δ (o V ... f))
        δ)   
   (--> (begin V E) E begin)
   (--> (let x V E)
        (subst x V E) let)))
  
(test--> v (term ((-- (λ x 0)) (-- 1) †)) (term 0))
(test--> v 
         (term ((-- (λ f x (f x †))) (-- 0) †))
         (term ((-- (λ f x (f x †))) (-- 0) †)))                 
(test--> v (term ((-- 0) (-- 1) †)) (term (blame † Λ (-- 0) λ (-- 0))))
(test--> v (term (if (-- 0) 1 2)) (term 1))
(test--> v (term (if (-- #t) 1 2)) (term 1))
(test--> v (term (if (-- #f) 1 2)) (term 2))
(test--> v (term (add1 (-- 0) †)) (term (-- 1)))
(test--> v (term (proc? (-- #f) †)) (term (-- #f)))
(test--> v (term (proc? (-- (λ x x)) †)) (term (-- #t)))
(test--> v (term (proc? (-- (λ f x x)) †)) (term (-- #t)))
(test--> v (term (proc? (-- (any/c -> any/c)) †)) (term (-- #t)))


(define -->_v (context-closure v λc~ 𝓔))

(test-->> -->_v (term ((λ x 0) 1 †)) (term (-- 0)))                
(test-->> -->_v (term (0 1 †)) (term (blame † Λ (-- 0) λ (-- 0))))
(test-->> -->_v (term (if 0 1 2)) (term (-- 1)))
(test-->> -->_v (term (if #t 1 2)) (term (-- 1)))
(test-->> -->_v (term (if #f 1 2)) (term (-- 2)))
(test-->> -->_v (term (add1 0 †))  (term (-- 1)))
(test-->> -->_v (term (proc? #f †)) (term (-- #f)))

(define c
  (reduction-relation
   λc~ #:domain E
   (--> (((C_1 --> C_2) <= f_1 f_2 V_1 f_3 W) V_2 f_4)
        (C_2 <= f_1 f_2 V_1 f_3 (W (C_1 <= f_2 f_1 V_2 f_3 V_2) f_4))
        split)   
   (--> (int/c <= f_1 f_2 V f_3 aint) 
        (remember-contract aint int/c) 
        chk-int-pass)
   (--> (int/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 int/c V_2)
        (side-condition (not (aint? (term V_2))))
        chk-int-fail)
   (--> (none/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 none/c V_2)
        chk-none-fail)
   (--> (string/c <= f_1 f_2 V f_3 astring) 
        (remember-contract astring string/c)
        chk-string-pass)   ;; new
   (--> (string/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 string/c V_2)
        (side-condition (not (astring? (term V_2))))
        chk-string-fail)   
   (--> (bool/c <= f_1 f_2 V f_3 abool)
        (remember-contract abool bool/c)
        chk-bool-pass)   ;; new
   (--> (bool/c <= f_1 f_2 V_1 f_3 V_2) 
        (blame f_1 f_3 V_1 bool/c V_2)
        (side-condition (not (abool? (term V_2))))
        chk-bool-fail)   
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 W)
        ((C_1 --> C_2) <= f_1 f_2 V f_3 W)
        chk-fun-pass-proc)
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 WFV)
        (blame f_1 f_3 V (C_1 -> C_2) WFV)
        chk-fun-fail-flat)   
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 W?)
        ((C_1 --> C_2) <= f_1 f_2 V f_3 (remember-contract W? (none/c -> any/c)))
        (side-condition (not (redex-match λc~ W (term W?))))
        chk-fun-pass-maybe-proc)
   (--> ((C_1  -> C_2) <= f_1 f_2 V f_3 W?)
        (blame f_1 f_3 V (C_1 -> C_2) W?)
        (side-condition (not (redex-match λc~ W (term W?))))
        chk-fun-fail-maybe-proc)      
   (--> ((pred SV) <= f_1 f_2 V_1 f_3 V_2)
        (if (SV V_2 Λ) 
            (remember-contract V_2 (pred SV))
            (blame f_1 f_3 V_1 (pred SV) V_2))
        ;; Only want smart to fire when condition holds
        (side-condition 
         (not (redex-match λc~ 
                           ((pred (f_a ^ f_b)) <= f_1* f_2* V_* f_3* (-- C_0 ... (pred (f_a ^ f_c)) C_1 ...))
                           (term ((pred SV) <= f_1 f_2 V_1 f_3 V_2)))))
        chk-pred-c)   
   
   ;; sugar
   (--> (any/c <= f_1 f_2 V_1 f_3 V_2) V_2 any-pass)))

(test--> c 
         (term (((any/c --> any/c) <= f g (-- 7) f (-- (λ x 5))) (-- 8) †))
         (term (any/c <= f g (-- 7) f ((-- (λ x 5)) (any/c <= g f (-- 8) f (-- 8)) †))))
(test--> c (term (int/c <= f g (-- 0) f (-- 5))) (term (-- 5 int/c)))
(test--> c 
         (term (int/c <= f g (-- 0) f (-- (λ x x))))
         (term (blame f f (-- 0) int/c (-- (λ x x)))))
(test--> c 
         (term (int/c <= f g (-- 0) f (-- #t))) 
         (term (blame f f (-- 0) int/c (-- #t))))
(test--> c
         (term ((any/c  -> any/c) <= f g (-- 0) f (-- (λ x x))))
         (term ((any/c --> any/c) <= f g (-- 0) f (-- (λ x x)))))
(test--> c 
         (term ((any/c  -> any/c) <= f g (-- 0) f (-- 5)))
         (term (blame f f (-- 0) (any/c -> any/c) (-- 5))))
(test--> c
         (term ((pred (λ x 0)) <= f g (-- 0) f (-- 5)))
         (term (if ((λ x 0) (-- 5) Λ)
                   (-- 5 (pred (λ x 0)))
                   (blame f f (-- 0) (pred (λ x 0)) (-- 5)))))

(define c~
  (reduction-relation
   λc~ #:domain E
   ;; IMPROVE ME: for all (C_1 -> C_2) in C ..., you know C_2 of result.
   (--> ((-- (pred SV) C ...) V f)
        (begin ((demonic (pred SV)) V ★) (-- any/c))
        (side-condition (not (abstract-value? (term V))))
        apply-abs-pred-concrete)
   (--> ((-- (pred SV) C ...) (-- C_0 ...) f)
        (-- any/c)
        apply-abs-pred-abs)
        
   ;; IMPROVE ME: for all (C_1 -> C_2) in C ..., you know C_2 of result.
   (--> ((-- (C_1 -> C_2) C ...) V f)
        (begin ((demonic C_1) V #;(C_1 <= f ★ V f V) ★) (-- C_2))
        (side-condition (not (abstract-value? (term V))))
        apply-abs-func-concrete) 
   (--> ((-- (C_1 -> C_2) C ...) (-- C_0 ...) f)  
        #;(begin (C_1 <= f ★ (-- C_0 ...) f (-- C_0 ...))
                 (-- C_2))
        (-- C_2)
        apply-abs-func-abs)   
   (--> ((-- int/c) V)
        (blame f Λ (-- int/c) λ (-- int/c))
        apply-abs-int)
   (--> (if (-- C C_0 ...) E_1 E_2)
        E_2
        if-abs-false)
   (--> (if (-- C C_0 ...) E_1 E_2)
        E_1
        if-abs-true)
   (--> (int/c <= f_1 f_2 V f_3 (-- int/c))
        (-- int/c)
        check-int-abs-int)
   (--> (int/c <= f_1 f_2 V f_3 (-- (pred SV) C ...))
        (-- int/c (pred SV) C ...)
        check-int-abs-pred-pass)
   (--> (int/c <= f_1 f_2 V f_3 (-- (pred SV) C ...))
        (blame f_1 f_3 V int/c (-- (pred SV) C ...))
        check-int-abs-pred-fail)
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- (pred SV) C ...))
        (-- (C_1 -> C_2) (pred SV) C ...)
        check-func-abs-pred-pass)
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- (pred SV) C ...))
        (blame f_1 f_3 V (C_1 -> C_2) (-- (pred SV) C ...))
        check-func-abs-pred-fail)
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- int/c C ...))
        (blame f_1 f_3 V (C_1 -> C_2) (-- int/c C ...))
        check-func-abs-int-fail)
   
   (--> (C <= f_1 f_2 V f_3 (-- C_0 ... C C_1 ...))
        (-- C_0 ... C C_1 ...)
        (side-condition (not (redex-match λc~ (C_a -> C_b) (term C))))
        smart*)
   
   ;; Possible overlapping
   (--> ((pred (f_a ^ f_b)) <= f_1 f_2 V f_3 (-- C_0 ... (pred (f_a ^ f_c)) C_1 ...))
        (-- C_0 ... (pred (f_a ^ f_b)) C_1 ...)
        (side-condition (not (eq? (term f_b) (term f_c))))
        smart*-pred-mod)
   
   ;; sugar
   #;
   (--> ((-- any/c) V f)
        (begin ((demonic any/c) V ★) (-- any/c)))
   
   (--> ((-- any/c C ...) V f)
        (begin ((demonic any/c) V ★) (-- any/c))
        (side-condition (not (abstract-value? (term V))))
        apply-abs-any-concrete)
   (--> ((-- any/c C ...) (-- C_0 ...) f)
        (-- any/c)
        apply-abs-any-abs)      
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- any/c))
        (blame f_1 f_3 V (C_1 -> C_2) (-- any/c)))   
   (--> ((C_1 -> C_2) <= f_1 f_2 V f_3 (-- any/c))
        (-- (C_1 -> C_2)))
   (--> (int/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (-- int/c C ...))
   (--> (int/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (blame f_1 f_3 V int/c (-- any/c C ...)))
   (--> (bool/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (-- bool/c C ...))
   (--> (bool/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (blame f_1 f_3 V bool/c (-- any/c C ...)))
   (--> (string/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (-- string/c C ...))   
   (--> (string/c <= f_1 f_2 V f_3 (-- any/c C ...))
        (blame f_1 f_3 V string/c (-- any/c C ...)))))

(define (Δ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f ^ f)
        (-- PV)
        (where (M_1 ... (module f C PV) M_2 ...) ,Ms)
        Δ-self)
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 (-- PV) f_1 (-- PV))
        (where (M_1 ... (module f_1 C PV) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2))))
        Δ-other)))

(test--> (Δ (term [(module f any/c 0)]))
         (term (f ^ f))
         (term (-- 0)))
(test--> (Δ (term [(module f any/c 0)]))
         (term (f ^ g))
         (term (any/c <= f g (-- 0) f (-- 0))))

(define (Δ~ Ms)
  (reduction-relation
   λc~ #:domain E
   (--> (f ^ f)
        V
        (where (M_1 ... (module f C V) M_2 ...) ,Ms)
        self-mod-ref)
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 (-- PV) f_1 (-- PV))
        (where (M_1 ... (module f_1 C PV) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2))))
        concrete-mod-ref)
   (--> (f_1 ^ f_2)
        (C <= f_1 f_2 (-- C) f_1 (-- C))
        #;(-- C)
        (where (M_1 ... (module f_1 C ☁) M_2 ...) ,Ms)
        (side-condition (not (eq? (term f_1) (term f_2))))
        opaque-mod-ref)))

(test--> (context-closure (Δ~ (term [(module prime? any/c ☁)])) λc~ 𝓔)
         (term ((prime? ^ rsa)
                (--
                 (pred
                  (prime? ^ keygen)))
                Λ))         
         (term ((any/c <= prime? rsa (-- any/c) prime? (-- any/c))
                (--
                 (pred
                  (prime? ^ keygen)))
                 Λ)))

(test--> (Δ~ (term [(module prime? any/c ☁)]))
         (term (prime? ^ rsa))
         (term (any/c <= prime? rsa (-- any/c) prime? (-- any/c))))

(test--> (Δ~ (term [(module f any/c ☁)]))
         (term (f ^ g))
         (term (any/c <= f g (-- any/c) f (-- any/c))))

;; when we get blame, discard the context
(define error-propagate
  (reduction-relation 
   λc~ #:domain E
   (--> (in-hole 𝓔 (-- any_0 ... none/c any_1 ...))
        (-- any_0 ... none/c any_1 ...)
        (side-condition (not (equal? (term hole) (term 𝓔))))
        halt-none/c)
   (--> (in-hole 𝓔 B) B
        (side-condition (not (equal? (term hole) (term 𝓔))))
        halt-blame)
   (--> (-- any C_0 C ...) (-- any) forget))) ;; Maybe you want to not forget


(define (-->_vcΔ Ms)
  (union-reduction-relations error-propagate (context-closure (union-reduction-relations v c (Δ Ms)) λc~ 𝓔)))

(define (-->_vcc~Δ Ms)
  (union-reduction-relations error-propagate (context-closure (union-reduction-relations v c c~ (Δ~ Ms)) λc~ 𝓔)))

(define-syntax-rule (test-->>p p e ...)
  (test-->> (-->_vcc~Δ (all-but-last p)) (last p)
            e ...))

 
(test-->>p fit-example (term (-- string/c)))
(test-->>p fit-example-keygen-string
           (term (blame keygen prime? (-- "Key") int/c (-- "Key"))))
(test-->>p fit-example-rsa-7
           (term (-- string/c))
           (term (blame keygen keygen (-- (λ x 7)) (pred (prime? ^ keygen)) (-- 7))))

(test-->>p example-8 (term (blame h g (-- #f) (pred (λ x x)) (-- #f))))
(test-->>p example-8-opaque 
           (term (-- any/c))
           (term (blame h g (-- any/c) (pred (λ x x)) (-- any/c))))
