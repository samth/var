#lang racket

(require redex)
(require (only-in "lang.rkt" scpcf [ev ev1]))


(define-extended-language cr scpcf
  [e ....
     (let [x e] e)
     (let ([x e] [x e] ...) e)
     (or e e ...)
     (and e e ...)
     (begin e e ...)
     (cond [e e] ... [else e])])

(define-metafunction cr
  desug : e -> e
  [(desug (λ x e)) (λ x (desug e))]
  [(desug a) a]
  [(desug x) x]
  [(desug (e_0 e_1 e_2 ...)) ((desug e_0) (desug e_1) (desug e_2) ...)]
  [(desug (if e e_1 e_2)) (if (desug e) (desug e_1) (desug e_2))]
  [(desug (mon c e)) (mon (desug-c c) (desug e))]
  [(desug (μ x e)) (μ x (desug e))]
  [(desug (and e)) (desug e)]
  [(desug (and e_1 e_2 ...)) (if (desug e_1) (desug (and e_2 ...)) #f)]
  [(desug (or e)) (desug e)]
  [(desug (or e_1 e_2 ...))
   ((λ x_tmp (if x_tmp x_tmp (desug (or e_2 ...)))) (desug e_1))
   (where x_tmp ,(variable-not-in (term (e_1 e_2 ...)) (term tmp)))]
  [(desug (let [x e_x] e)) ((λ x (desug e)) (desug e_x))]
  [(desug (let ([x e_x]) e)) ((λ x (desug e)) (desug e_x))]
  [(desug (let ([x_1 e_1] [x_2 e_2] ...) e))
   ((λ x_1 (desug (let ([x_2 e_2] ...) e))) (desug e_1))]
  [(desug (cond [else e])) (desug e)]
  [(desug (cond [e_1 e_2] any ...))
   (if (desug e_1) (desug e_2) (desug (cond any ...)))]
  [(desug (begin e)) (desug e)]
  [(desug (begin e_1 e_2 ...))
   ((λ x_tmp (desug (begin e_2 ...))) (desug e_1))
   (where x_tmp ,(variable-not-in (term (e_1 e_2 ...)) (term tmp)))])

(define-metafunction cr
  desug-c : c -> c
  [(desug-c (flat e)) (flat (desug e))]
  [(desug-c (or/c c_1 c_2)) (or/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (and/c c_1 c_2)) (and/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (cons/c c_1 c_2)) (cons/c (desug-c c_1) (desug-c c_2))]
  [(desug-c (c_x ↦ (λ x c_y))) ((desug-c c_x) ↦ (λ x (desug-c c_y)))]
  [(desug-c (μ x c)) (μ x (desug-c c))]
  [(desug-c x) x])

(define-metafunction cr
  ev : e -> (EA ...)
  [(ev e) (ev1 (desug e))])

; f : (∪ int? str?) → int?
; for example 2
(define f
  (term (λ xf
          (if (int? xf) (add1 xf) (str-len xf)))))

; strnum? : ⊤ → Bool
(define strnum?
  (term (λ x⊤ (or (str? x⊤) (int? x⊤)))))

; carnum? : (cons ⊤ ⊤) -> Bool
(define carnum?
  (term (λ xcn (int? (car xcn)))))

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
    → {(• int?) "not tested" blame}]
   
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
    → {#t blame}]
   
   ; with contracts
   [(mon (flat int?) •) → {blame (• int?)}]
   [(mon (μ list? (or/c (flat false?) (cons/c (flat int?) list?)))
         #f) → {#f}]
   [(mon (μ list? (or/c (flat false?) (cons/c (cons/c (flat int?) (flat int?)) list?)))
         (cons • #f)) → {(Cons (Cons (• int?) (• int?)) #f) blame}]
   
   ; check for proper list (with safe counter to make sure it terminates)
   #;[(let (proper-list? (μ (check)
                            (λ l
                              (λ n
                                (cond
                                  [(zero? n) "killed"]
                                  [else (or (false? l)
                                            (and (cons? l)
                                                 ((check (cdr l)) (sub1 n))))])))))
        ((proper-list? •) 7))
      → {#t #f "killed"}]
   
   ; 'lastpair' from Wright paper (with a safe counter to make sure it terminates)
   #;[(let [lastpair (μ (lp)
                        (λ s
                          (λ n
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
                 (λ y1 x)
                 (λ y2 1)))
           •))
    → {#t}]
   
   
   ;; Chugh paper examples:
   ; negate, section 2.1
   ,@ (let* ([bool? (term (λ xb (or (true? xb) (false? xb))))]
             [negate (term (λ x
                             (cond
                               [(int? x) (+ 0 x)] ; i don't have "-"
                               [(,bool? x) (false? x)]
                               [else blame])))])
        (term {[(int? (,negate ((λ z (if (int? z) z 42)) •))) → {#t}]
               [(,negate #t) → {#f}]}))
   
   ;; Linear-log paper examples:
   [(let [x (cons • •)] (car x)) → {•}]
   [(let [x •] (if (cons? x) (car x) #f)) → {• #f}]
   [(let [x •]
      ; i replace the latter (car x) with (cons? x)
      ; cos i don't know a more obvious way to reflect the
      ; learned info in the result
      (begin [cdr x] [cons? x]))
    → {blame #t}]
   [(let ([x •]
          [g (λ y (+ (car y) 1))])
      ; i wanna strengthen the original example a bit:
      ; if the program survives the call to g, not only
      ; we know x is a pair, but also its car an int
      (begin [g x]
             [and (cons? x) (int? (car x))]))
    → {blame #t}])))

(test-results)