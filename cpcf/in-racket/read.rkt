#lang racket
(require "lang.rkt")
(require "prim.rkt")
(require redex)

(provide
 (contract-out
  [read-p (any/c . -> . PROG?)]
  [read-e (any/c . -> . exp?)]
  [read-c (any/c . -> . con?)]))

(define hash0 (hash))
(define modls0 hash0)

;; read-p : S-exp -> Prog
(define read-p
  (match-lambda
    [`(,m ... (require ,reqs ...) ,e)
     (match-let ([modls (read-ms m modls0)])
       (PROG modls (read-e e '† modls reqs ∅)))]
    [`(,m ... ,e) (read-p `(,@ m (require) ,e))]
    [s (error "Invalid program form:" s)]))

;; read-modl : S-exp -> [Hashtable Symbol Module]
(define (read-ms s ms)
  
  ;; m-pass-1 : S-exp Modules -> Modules
  (define (m-pass-1 m ms)
    (match-let ([`(module ,n ,d ...) m])
      (hash-set ms n (ds-pass-1 d (MODL n hash0 hash0)))))
  
  ;; ds-pass-1 : [Listof S-exp] Module -> Module
  (define (ds-pass-1 ds m)
    (foldl d-pass-1 m ds))
  
  ;; d-pass-1 : S-exp Module -> Module
  (define (d-pass-1 s m)
    (match* (s m)
      [(`(define (,f ,x ...) ,_) _) (d-pass-1 `(define ,f •) m)]
      [(`(define ,x ,_) (MODL n decs defs)) (MODL n decs (hash-set defs x #f))]
      [(`(provide (,x ,_) ...) _)
       (foldl (match-lambda**
               [(x (MODL n decs defs)) (MODL n (hash-set decs x C/ANY) defs)])
              m x)]
      [(`(require ,_ ...) m) m] ; ignore
      [(_ _) (error "Invalid module body form:" s)]))
  
  ;; m-pass-2 : S-exp Modules -> Modules
  (define (m-pass-2 m ms)
    
    ;; ds-pass-2 : [Listof S-exp] Module -> Module
    (define (ds-pass-2 reqs ds m)
      
      ;; d-pass-2 : S-exp Module -> Module
      (define (d-pass-2 d m)
        (match* (d m)
          [(`(define (,f ,x ...) ,e) _)
           (d-pass-2 `(define ,f (λ ,x ,e)) m)]
          [(`(define ,x ,e) (MODL n decs defs))
           (MODL n decs (hash-set defs x (read-e e n ms reqs ∅)))]
          [(`(provide ,pr ...) (MODL n decs defs))
           (foldl (match-lambda**
                   [(`(,x ,c) (MODL n decs defs))
                    (MODL n (hash-set decs x (read-c c n ms reqs ∅)) defs)])
                  m pr)]
          [(_ _) (error "Invalid module body form:" d)]))
      
      (foldl d-pass-2 m ds))
    
    (match m
      [`(module ,n (require ,reqs ...) ,d ...)
       (hash-update ms n (λ (m) (ds-pass-2 reqs d m)))]
      [`(module ,n ,d ...) (m-pass-2 `(module ,n (require) ,@ d) ms)]))
  
  
  
  ;; ms-pass-2 : S-exp -> Modules
  (foldl m-pass-2 (foldl m-pass-1 ms s) s))

;; S-exp Symbol [Hashtable Symbol Module] [Listof Symbol] [Setof Symbol] -> Exp
(define (read-e s [modl-name '†] [modls modls0] [reqs '()] [bound ∅])
  ;; short-hand for recursion with same accumulators
  (define (loop s) (read-e s modl-name modls reqs bound))
  
  (match s
    ;; syntactic sugar
    [`(begin ,e) (loop e)]
    [`(begin ,e ,e1 ...) (let ([x (fresh-x e1)])
                           (loop `(let [,x ,e] ,@ e1)))]
    [`(let [,x ,e] ,e1) (loop `((λ (,x) ,e1) ,e))]
    [`(let ([,x ,e]) ,e1) (loop `((λ (,x) ,e1) ,e))]
    [`(let ([,x ,e] ,bindings ...) ,e1) (loop `((λ (,x) (let bindings ,e1)) ,e))]
    [`(and ,e) (loop e)]
    [`(and ,e ,e1 ...) (loop `(if ,e (and ,@ e1) #f))]
    [`(or ,e) (loop e)]
    [`(or ,e ,e1 ...) (let ([x (fresh-x e1)])
                        (loop `(let [,x ,e] (if x x (or ,@ e1)))))]
    [`(cond [else ,e]) (loop e)]
    [`(cond [,e1 ,e2] ,otherwise ...) (loop `(if ,e1 ,e2 (cond ,@ otherwise)))]
    
    ;; special forms
    [`(if ,e1 ,e2 ,e3) (IF (loop e1) (loop e2) (loop e3))]
    [`(μ (,x) ,e) (MU x (read-e e modl-name modls reqs (set-add bound x)))]
    [`(mon ,lo ,l+ ,l- ,c ,e)
     (MON lo l+ l-
          (read-c c modl-name modls reqs bound)
          (loop e))]
    [`(λ (,x ... ,z ..) ,e)
     (if (and (symbol? z) (andmap symbol? x))
         (let ([params (append x (list z))])
           (LAM params
                (read-e e modl-name modls reqs (set-union (list->set params) bound))
                #t))
         (error "Invalid var-λ variable declaration:" x z))]
    [`(λ (,x ...) ,e)
     (if (andmap symbol? x)
         (LAM x (read-e e modl-name modls reqs (set-union (list->set x) bound)) #f)
         (error "Invalid λ variable declaration:" x))]
    
    ;; application
    [`(,f ,xs ...) (AP (loop f) (map loop xs))]
    
    ;; variables / other values
    ['• (OPQ)]
    [x (cond
         [(symbol? x) (resolve-id modl-name modls reqs bound x)]
         [(base? x) x]
         [else (error "Invalid expression form:" x)])]))

;; S-exp Symbol [Hashtable Symbol Module] [Setof Symbol] [Setof Symbol] -> Contract
(define (read-c s [modl-name '†] [modls modls0] [reqs '()] [bound ∅])
  (define (loop x) (read-c x modl-name modls reqs bound))
  (match s
    [`(or/c ,c1 ,c2) (OR/C (loop c1) (loop c2))]
    [`(and/c ,c1 ,c2) (AND/C (loop c1) (loop c2))]
    [`(cons/c ,c1 ,c2) (STRUCT/C 'cons (list [loop c1] [loop c2]))]
    [`(struct/c ,t ,cs ...) (STRUCT/C t (map loop cs))]
    [`(,c1 ... ,c1′ .. ↦ (λ (,x ...) ,c2))
     (FUNC/C (map list x (append (map loop c1) (list (loop c1′))))
             (read-c c2 modl-name modls reqs (set-union (list->set x) bound))
             #t)]
    [`(,c1 ... ↦ (λ (,x ...) ,c2))
     (FUNC/C (map list x (map loop c1))
             (read-c c2 modl-name modls reqs (set-union (list->set x) bound))
             #f)]
    [`(,c1 ... ,c1′ .. ↦ ,c2) (let ([xs (fresh-xs (length `(,@ c1 ,c1′)) s)])
                                (loop `(,@ c1 ,c1′ ↦ (λ ,xs ,c2))))]
    [`(,c1 ... ↦ ,c2) (let ([xs (fresh-xs (length c1) c2)])
                        (loop `(,@ c1 ↦ (λ ,xs ,c2))))]
    [`(μ (,x) ,c) (MU/C x (read-c c modl-name modls reqs (set-add bound x)))]
    [e (FLAT/C (read-e e modl-name modls reqs bound))]))



;; Symbol Modules [Listof Symbol] [Setof Symbol] Symbol -> Exp
;; checks whether the identier can be found in any required module
(define (resolve-id from modls reqs bound name)
  (cond
    ; local variable
    [(set-member? bound name) name]
    ; same module reference
    [(and (modls-has? modls from) (modl-defines? (hash-ref modls from) name))
     (M-REF from from name)]
    ; from different module
    [else
     (let ([ref (for/fold ([ref '∅]) ([r reqs])
                  (if (modl-exports? (hash-ref modls r) name)
                      (M-REF from r name)
                      '∅))])
       (cond
         ; cross module reference
         [(M-REF? ref) ref]
         ; primitive
         [else
          (match name
            ['cons CONS]
            ['cons? CONS?]
            ['car CAR]
            ['cdr CDR]
            [(? prim? x) (match (∆ x)
                           [#f x]
                           [c (MON '∆ '∆ from c x)])]
            [_ (error "Unknown identifier:" name)])]))]))


;; returns fresh variable(s) not in given term
(define (fresh-x e)
  (variable-not-in e 'tmp))
(define (fresh-xs n e)
  (variables-not-in e (make-list n 'tmp)))
