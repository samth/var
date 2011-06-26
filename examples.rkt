#lang racket
(require redex/reduction-semantics)
(require "lang.rkt" "util.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test examples)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples and tests

;; Modified from Figure 8 in paper (8 -> #f).
(define example-8-raw
  (term [(module f (anything -> (anything -> anything)) (λ (x) x))
         (module g ((pred (λ (x) x)) -> nat?) (λ (x) 0))
         (module h anything (λ (z) ((f g) #f)))
         (h 0)]))

(define example-8
  (term [(module f ((any/c) -> ((any/c) -> (any/c))) (λ (x) x))
         (module g ((pred (λ (x) x) g) -> (nat/c)) (λ (x) 0))
         (module h (any/c) (λ (z) (@ (@ (f ^ h) (g ^ h) h) #f h)))
         (@ (h ^ †) 0 †)]))

(define example-8-opaque-raw
  (term [(module f (anything -> (anything -> anything)) ☁)
         (module g ((pred (λ (x) x)) -> nat?) ☁)
         (module h anything (λ (z) ((f g) #f)))
         (h 0)]))

(define example-8-opaque
  (term [(module f ((any/c) -> ((any/c) -> (any/c))) ☁)
         (module g ((pred (λ (x) x) g) -> (nat/c)) ☁)
         (module h (any/c) (λ (z) (@ (@ (f ^ h) (g ^ h) h) #f h)))
         (@ (h ^ †) 0 †)]))

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

(define mod-prime-raw  (term (module prime? (nat? -> anything) ☁)))
(define mod-rsa-raw    (term (module rsa ((pred prime?) -> (string? -> string?)) ☁)))
(define mod-keygen-raw (term (module keygen (anything -> (pred prime?)) ☁)))
(define mod-keygen-7-raw (term (module keygen (anything -> (pred prime?)) (λ (x) 7))))
(define mod-keygen-str-raw (term (module keygen (anything -> (pred prime?)) (λ (x) "Key"))))
(define top-fit-raw (term ((rsa (keygen #f)) "Plain")))

(define mod-prime  (term (module prime? ((pred nat? prime?) -> (pred (λ (x) #t) prime?)) ☁)))
(define mod-rsa    (term (module rsa ((pred (prime? ^ rsa) rsa) -> ((pred string? rsa) -> (pred string? rsa))) ☁)))
(define mod-keygen (term (module keygen ((pred (λ (x) #t) keygen) -> (pred (prime? ^ keygen) keygen)) ☁)))
(define mod-keygen-7 (term (module keygen ((pred (λ (x) #t) keygen) -> (pred (prime? ^ keygen) keygen)) (λ (x) 7))))
(define mod-keygen-str (term (module keygen ((pred (λ (x) #t) keygen) -> (pred (prime? ^ keygen) keygen)) (λ (x) "Key"))))
(define top-fit (term (@ (@ (rsa ^ †) (@ (keygen ^ †) #f †) †) "Plain" †)))

(define fit-example-raw
  (term [,mod-prime-raw ,mod-rsa-raw ,mod-keygen-raw ,top-fit-raw]))

(define fit-example
  (term [,mod-prime ,mod-rsa ,mod-keygen ,top-fit]))

(define fit-example-rsa-7-raw
  (term [,mod-prime-raw ,mod-rsa-raw ,mod-keygen-7-raw ,top-fit-raw]))

(define fit-example-rsa-7
  (term [,mod-prime ,mod-rsa ,mod-keygen-7 ,top-fit]))

;; Should see keygen break contract with prime?.
(define fit-example-keygen-string-raw
  (term [,mod-prime-raw ,mod-rsa-raw ,mod-keygen-str-raw ,top-fit-raw]))

(define fit-example-keygen-string
  (term [,mod-prime ,mod-rsa ,mod-keygen-str ,top-fit]))

(define fit-example-alt
  (term [,mod-prime 
         ,mod-rsa
         ,mod-keygen 
         (@ (@ (rsa ^ †) "Plain" †) (@ (keygen ^ †) #f †) †)]))

(define list-id-example-raw
  (term [(module id 
           anything
           (λ (ls)
             (if (empty? ls) 
                 ls 
                 (cons (first ls) 
                       (id (rest ls))))))
         (id (cons 1 (cons 2 (cons 3 empty))))]))

(define list-id-example
  (term [(module id 
           (pred (λ (x) #t) id)
           (λ (ls)
             (if (@ empty? ls id)
                 ls 
                 (@ cons 
                    (@ first ls id)
                    (@ (id ^ id) (@ rest ls id) id)
                    id))))
         (@ (id ^ †) (@ cons 1 (@ cons 2 (@ cons 3 empty †) †) †) †)]))

(define list-of-nat/c
  (term (rec/c x (or/c (empty/c)
                       (cons/c (nat/c) x)))))               

(define list-id-example-contract
  (term [(module id 
           (,list-of-nat/c -> ,list-of-nat/c)
           (λ (ls)
             (if (@ empty? ls id)
                 ls 
                 (@ cons 
                    (@ first ls id)
                    (@ (id ^ id) (@ rest ls id) id)
                    id))))
         (@ (id ^ †) (@ cons 1 (@ cons 2 (@ cons 3 empty †) †) †) †)]))


(define list-rev-example-raw
  (term [(module rev
           anything
           (λ (ls)
             ((λ rev* (ls r*)
                   (if (empty? ls)
                       r*
                       (rev* (rest ls) (cons (first ls) r*))))
               ls empty)))
         (rev (cons 1 (cons 2 (cons 3 empty))))]))

(define cons/c-example-raw
  (term [(module p
           (cons/c nat? nat?)
           (cons (-- 1) (-- 2)))
         (first p)]))

(define nat/c-example-raw
  (term [(module n nat? 5) n]))

(define rec/c-example-raw
  (term [(module n nat? 5)
         (module l (flat-rec/c X (or/c empty? (cons/c nat? X)))
           (cons 1 (cons n empty)))
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

