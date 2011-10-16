#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test examples)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples and tests

;; Modified from Figure 8 in paper (8 -> #f).
(define example-8-raw
  (term [(module f racket (require) (define (f x) x) (provide/contract [f (anything -> (anything -> anything))]))
         (module g racket (require) (define (g x) 0) (provide/contract [g ((pred (λ (x) x)) -> exact-nonnegative-integer?)]))
         (module h racket (require (only-in f f) (only-in g g)) (define (h z) ((f g) #f)) (provide/contract [h anything]))
         (require (only-in h h))
         (h 0)]))

;; a module with one export, named the same as the module
(define-metafunction λc~
  simple-module : f any any -> any
  [(simple-module f any_C any)
   (module f racket (require) (define f any) (provide/contract [f any_C]))])

(define example-8
  (term [(simple-module f ((any/c) -> ((any/c) -> (any/c))) (λ (x) x))
         (simple-module g ((pred (λ (x) x) g) -> (nat/c)) (λ (x) 0))
         (module h racket (require (only-in f f) (only-in g g)) (define h (λ (z) (@ (@ (f ^ h f) (g ^ h g) h) #f h))) (provide/contract [h (any/c)]))
         (require (only-in h h))
         (@ (h ^ † h) 0 †)]))

(define example-8-opaque-raw
  (term [(simple-module f (anything -> (anything -> anything)) ☁)
         (simple-module g ((pred (λ (x) x)) -> exact-nonnegative-integer?) ☁)
         (module h racket (require (only-in f f) (only-in g g)) (define h (λ (z) ((f g) #f))) (provide/contract [h anything]))
         (require (only-in h h))
         (h 0)]))

(define example-8-opaque
  (term [(simple-module f ((any/c) -> ((any/c) -> (any/c))) ☁)
         (simple-module g ((pred (λ (x) x) g) -> (nat/c)) ☁)
         (module h racket (require (only-in f f) (only-in g g)) (define h (λ (z) (@ (@ (f ^ h f) (g ^ h g) h) #f h))) (provide/contract [h (any/c)]))
         (require (only-in h h))
         (@ (h ^ † h) 0 †)]))

(test
 (test-predicate (redex-match λc-user M) (first example-8))
 (test-predicate (redex-match λc-user M) (second example-8))
 (test-predicate (redex-match λc-user M) (third example-8))
 (test-predicate (redex-match λc-user E) (last example-8))
 (test-predicate (redex-match λc~ P) example-8-opaque)
 (test-predicate (redex-match λc-user P) example-8)
 (test-predicate (redex-match λc P) example-8)
 (test-predicate (redex-match λc~ P) example-8) 
 (test-predicate (redex-match λc~ RP) example-8-raw)
 (test-predicate (redex-match λc~ RP) example-8-opaque-raw) 

 (test-predicate (redex-match λc-user C) (term ((pred (λ (x) x) ℓ) -> (nat/c)))))

(define mod-prime-raw  (term (simple-module prime? (exact-nonnegative-integer? -> anything) ☁)))
(define mod-rsa-raw    (term (simple-module rsa ((pred prime?) -> (string? -> string?)) ☁)))
(define mod-keygen-raw (term (simple-module keygen (anything -> (pred prime?)) ☁)))
(define mod-keygen-7-raw (term (simple-module keygen (anything -> (pred prime?)) (λ (x) 7))))
(define mod-keygen-str-raw (term (simple-module keygen (anything -> (pred prime?)) (λ (x) "Key"))))
(define top-fit-raw (term ((rsa (keygen #f)) "Plain")))

(define mod-prime  (term (simple-module prime? ((pred exact-nonnegative-integer? prime?) -> (pred (λ (x) #t) prime?)) ☁)))
(define mod-rsa    (term (simple-module rsa ((pred (prime? ^ rsa prime?) rsa) -> ((pred string? rsa) -> (pred string? rsa))) ☁)))
(define mod-keygen (term (simple-module keygen ((pred (λ (x) #t) keygen) -> (pred (prime? ^ keygen prime?) keygen)) ☁)))
(define mod-keygen-7 (term (simple-module keygen ((pred (λ (x) #t) keygen) -> (pred (prime? ^ keygen prime?) keygen)) (λ (x) 7))))
(define mod-keygen-str (term (simple-module keygen ((pred (λ (x) #t) keygen) -> (pred (prime? ^ keygen prime?) keygen)) (λ (x) "Key"))))
(define top-fit (term (@ (@ (rsa ^ † rsa) (@ (keygen ^ † keygen) #f †) †) "Plain" †)))

(define fit-require (term (require (only-in rsa rsa) (only-in keygen keygen))))

(define fit-example-raw
  (term [,mod-prime-raw ,mod-rsa-raw ,mod-keygen-raw ,fit-require ,top-fit-raw]))

(define fit-example
  (term [,mod-prime ,mod-rsa ,mod-keygen ,fit-require ,top-fit]))

(define fit-example-rsa-7-raw
  (term [,mod-prime-raw ,mod-rsa-raw ,mod-keygen-7-raw ,fit-require ,top-fit-raw]))

(define fit-example-rsa-7
  (term [,mod-prime ,mod-rsa ,mod-keygen-7 ,fit-require ,top-fit]))

;; Should see keygen break contract with prime?.
(define fit-example-keygen-string-raw
  (term [,mod-prime-raw ,mod-rsa-raw ,mod-keygen-str-raw ,fit-require ,top-fit-raw]))

(define fit-example-keygen-string
  (term [,mod-prime ,mod-rsa ,mod-keygen-str ,fit-require ,top-fit]))

(define fit-example-alt
  (term [,mod-prime 
         ,mod-rsa
         ,mod-keygen 
         ,fit-require
         (@ (@ (rsa ^ † rsa) "Plain" †) (@ (keygen ^ † keygen) #f †) †)]))

(define list-id-example-raw
  (term [(simple-module id 
           anything
           (λ (ls)
             (if (empty? ls) 
                 ls 
                 (cons (first ls) 
                       (id (rest ls))))))
         (require (only-in id id))
         (id (cons 1 (cons 2 (cons 3 empty))))]))

(define list-id-example
  (term [(simple-module id 
           (pred (λ (x) #t) id)
           (λ (ls)
             (if (@ empty? ls id)
                 ls 
                 (@ cons 
                    (@ first ls id)
                    (@ (id ^ id id) (@ rest ls id) id)
                    id))))
         (require (only-in id id))
         (@ (id ^ † id) (@ cons 1 (@ cons 2 (@ cons 3 empty †) †) †) †)]))

(define list-of-nat/c
  (term (rec/c x (or/c (empty/c)
                       (cons/c (nat/c) x)))))               

(define list-id-example-contract
  (term [(simple-module id 
           (,list-of-nat/c -> ,list-of-nat/c)
           (λ (ls)
             (if (@ empty? ls id)
                 ls 
                 (@ cons 
                    (@ first ls id)
                    (@ (id ^ id id) (@ rest ls id) id)
                    id))))
         (require (only-in id id))
         (@ (id ^ † id) (@ cons 1 (@ cons 2 (@ cons 3 empty †) †) †) †)]))


(define list-rev-example-raw
  (term [(simple-module rev
           anything
           (λ (ls)
             ((λ rev* (ls r*)
                   (if (empty? ls)
                       r*
                       (rev* (rest ls) (cons (first ls) r*))))
               ls empty)))
         (require (only-in rev rev))
         (rev (cons 1 (cons 2 (cons 3 empty))))]))

(define cons/c-example-raw
  (term [(simple-module p
           (cons/c exact-nonnegative-integer? exact-nonnegative-integer?)
           (cons (-- 1) (-- 2)))
         (require (only-in p p))
         (first p)]))

(define nat/c-example-raw
  (term [(simple-module n exact-nonnegative-integer? 5) (require (only-in n n)) n]))

(define rec/c-example-raw
  (term [(simple-module n exact-nonnegative-integer? 5)
         (simple-module l (flat-rec/c X (or/c empty? (cons/c exact-nonnegative-integer? X)))
           (cons 1 (cons n empty)))
         (require (only-in l l))
         l]))

(test
 (test-predicate (redex-match λc~ RP) nat/c-example-raw) 
 
 (test-predicate (redex-match λc~ RP) list-id-example-raw)
 (test-predicate (redex-match λc~ P) list-id-example)
 
 (test-predicate (redex-match λc~ RP) list-rev-example-raw)
 (test-predicate (redex-match λc~ RP) cons/c-example-raw)
 
 (test-predicate (redex-match λc~ P) fit-example)
 (test-predicate (redex-match λc~ P) fit-example-alt)
 
 (test-predicate (redex-match λc~ RE) top-fit-raw)
 (test-predicate (redex-match λc~ RM) mod-prime-raw)
 (test-predicate (redex-match λc~ RM) mod-rsa-raw)
 (test-predicate (redex-match λc~ RM) mod-keygen-raw)
 (test-predicate (redex-match λc~ RM) mod-keygen-7-raw)
 (test-predicate (redex-match λc~ RM) mod-keygen-str-raw)
 
 (test-predicate (redex-match λc~ RP) fit-example-raw))

