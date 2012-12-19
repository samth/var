#lang racket
(require redex)
(require "lang.rkt")
(require "judgment.rkt")

(define-metafunction scpcf
  ; assume all variables have been (statically) renamed
  ev : e -> {ea ...}
  [(ev e)
   ,(rem-dup (term ((simplify Ans) ...)))
   (where (Ans ...) (step [] [] [] [] (desug e)))])

(define-metafunction scpcf
  step : Γ ρ O ψ e -> {Ans ...}
  [(step Γ ρ O ψ e)
   {Ans ...}
   (where {Ans ...} ,(judgment-holds (⇓ Γ ρ O ψ e Ans Γ o) Ans))])

(define-metafunction scpcf
  simplify : Ans -> ea
  [(simplify ERR) ERR]
  [(simplify ((λ (x) e) ρ O ψ)) function]
  [(simplify (op ρ O ψ)) function]
  [(simplify ((• CC ...) ρ O ψ)) ,(match (rem-dup (term (all-preds (CC ...))))
                                   ['() (term •)]
                                   [ps (term (• ,@ ps))])]
  [(simplify (Cons V_1 V_2)) (cons (simplify V_1) (simplify V_2))]
  [(simplify (any ρ O ψ)) any])

(define-metafunction scpcf
  all-preds : ((c ρ O ψ) ...) -> (p? ...)
  [(all-preds (((flat tt) ρ O ψ) any ...)) (all-preds (any ...))]
  [(all-preds (((flat p?) ρ O ψ) any ...))
   ,(cons (term p?) (term (all-preds (any ...))))]
  [(all-preds (any any_1 ...)) (all-preds (any_1 ...))]
  [(all-preds ()) ()])

; f : (∪ int? str?) → int?
; for example 2
(define f
  (term (λ (xf)
          (if (int? xf) (add1 xf) (str-len xf)))))

; strnum? : ⊤ → Bool
(define strnum?
  (term (λ (x⊤) (or (str? x⊤) (int? x⊤)))))

; carnum? : (cons ⊤ ⊤) -> Bool
(define carnum?
  (term (λ (xcn) (int? (car xcn)))))

(for-each
 (match-lambda
   [`(,e → ,r)
    (test-equal (list->set (term (ev ,e))) (list->set r))])
 (term
  (
   ; example 1
   [(let [x •]
      (if (int? x) (add1 x) 0))
    → {0 (• int?)}]
   
   ; example 2
   [(let [x •]
      (if (or (int? x) (str? x))
          (,f x)
          "not in f's domain"))
    → {(• int?) "not in f's domain"}]
   
   ; example 3, somewhat equivalent, cos i don't have 'member'
   [(let [z •]
      (let [x (cons? z)]
        (if x (cons? z) "FAIL")))
    → {#t "FAIL"}]
   
   ; example 4 (already tested in 2, actually)
   [(let [x •]
      (if (or (int? x) (str? x))
          (,f x)
          0))
    → {0 (• int?)}]
   
   ; example 5
   [(let ([x •] [y •])
      (if (or (int? x) (str? x)) ; assummption
          (if (and (int? x) (str? y))
              (+ x (str-len y))
              0)
          "not tested"))
    → {0 (• int?) "not tested"}]
   
   ; example 6
   [(let ([x •] [y •])
      (if (or (int? x) (str? x))
          (if (and (int? x) (str? y))
              (+ x (str-len y))
              (str-len x))
          "not tested"))
    → {(• int?) "not tested" ERR}]
   
   ; example 7 (no need to test actually, cos and is already a macro)
   [(let ([x •] [y •])
      (if (if (int? x) (str? y) #f)
          (+ x (str-len y))
          0))
    → {0 (• int?)}]
   
   ; example 8
   [(let [x •]
      (if (,strnum? x)
          (or (int? x) (str? x))
          "else"))
    → {#t "else"}]
   
   ; example 9 (no need for test, like and)
   [(let [x •]
      (if (let [tmp (int? x)]
            (if tmp tmp (str? x)))
          (,f x)
          0))
    → {0 (• int?)}]
   
   ; example 10
   [(let [p •]
      (if (cons? p)
          (if (int? (car p))
              (add1 (car p))
              7)
          "ignore"))
    → {7 (• int?) "ignore"}]
   
   ; example 11
   [(let [p (cons • •)]
      (if (and (int? (car p)) (int? (cdr p)))
          (and (int? (car p)) (int? (cdr p)))
          "else"))
    → {#t "else"}]
   
   ; example 12
   [(let [p (cons • •)]
      (if (,carnum? p)
          (int? (car p))
          "else"))
    → (#t "else")]
   
   ; example 13
   [(let ([x •] [y •])
      (cond
        [(and (int? x) (str? y)) (and (int? x) (str? y))]
        [(int? x) (and (int? x) (false? (str? y)))]
        [else #t]))
    → {#t}]
   
   ; example 14
   [(let ([input •] [extra •])
      (if (and (or (int? input) (str? input))
               (cons? extra))
          (cond
            [(and (int? input) (int? (car extra))) (+ input (car extra))]
            [(int? (car extra)) (+ (str-len input) (car extra))]
            [else 0])
          "ignore"))
    → {(• int?) 0 "ignore"}]
   
   ; information is represented in terms of farthest possible variable so it can
   ; be retained
   [(let (l (cons • •))
      (begin
        (let (x (car l))
          (if (int? x) "ignore" (add1 "raise error")))
        ; reached here, (car l) has to be nat
        (int? (car l))))
    → {#t ERR}]
   
   ; with contracts
   [(mon (flat int?) •)
    → {ERR (• int?)}]
   [(mon (flat int?) (• ,C/STR))
    → {ERR}]
   [(mon (flat int?) (• ,C/INT))
    → {(• int?)}]
   
   ; check for proper list (with safe counter to make sure it terminates)
   [(let (proper-list? (μ (check)
                          (λ (l)
                            (λ (n)
                              (cond
                                [(zero? n) "killed"]
                                [else (or (false? l)
                                          (and (cons? l)
                                               ((check (cdr l)) (sub1 n))))])))))
      ((proper-list? •) 7))
    → {#t #f "killed"}]
   
   ; 'lastpair' from Wright paper (with a safe counter to make sure it terminates)
   [(let [lastpair (μ (lp)
                      (λ (s)
                        (λ (n)
                          (cond
                            [(zero? n) "killed"]
                            [(cons? (cdr s)) ((lp (cdr s)) (sub1 n))]
                            [else s]))))]
      ((lastpair (cons • •)) 5))
    → {"killed" (cons • •)}]
   
   ; previously, precision was lost b/c Γ threw away stuff without 'flushing'
   ; them into the environment that closed λ
   [(int? ((let [x •]
             (if (int? x)
                 (λ (y) x)
                 (λ (y) 1)))
           •))
    → {#t}]
   
   
   ;; Chugh paper examples:
   ; negate, section 2.1
   ,@ (let ([negate (term (λ (x)
                            (cond
                              [(int? x) (- 0 x)]
                              [(bool? x) (false? x)]
                              [else "not in domain"])))])
        (term {[(,negate (• ,C/INT)) → {(• int?)}]
               [(,negate (• ,C/BOOL)) → {#t #f}]}))
   
   ;; Linear-log paper examples:
   ,@ (let ([read (term •)])
        (term {[(let [x (cons • •)] (car x))
                → {•}]
               [(let [x ,read]
                  (if (cons? x) (car x) #f))
                → {• #f}]
               [(let [x ,read]
                  ; i replace the latter (car x) with (cons? x)
                  ; cos i don't know a more obvious way to reflect the
                  ; learned info in the result
                  (begin [cdr x] [cons? x]))
                → {ERR #t}]
               [(let ([x ,read]
                      [g (λ (y) (+ (car y) 1))])
                  ; i wanna strengthen the original example a bit:
                  ; if the program survives the call to g, not only
                  ; we know x is a pair, but also its car an int
                  (begin [g x]
                         [and (cons? x) (int? (car x))]))
                → {ERR #t}]})))))

(test-results)