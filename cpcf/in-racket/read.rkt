#lang racket
(require "lang.rkt")
(require "prim.rkt")
(require redex)

(provide
 (contract-out
  [read-p (any/c . -> . PROG?)]
  [read-e ((any/c)
           (symbol? modls? [listof symbol?] [hash/c symbol? (or/c 'c 'e)])
           . ->* . exp?)]
  [read-c ((any/c)
           (symbol? modls? [listof symbol?] [hash/c symbol? (or/c 'c 'e)])
           . ->* . con?)]
  [α-rename-p (PROG? . -> . PROG?)]
  [α-rename-e (exp? . -> . exp?)]
  [α-rename-c (con? . -> . con?)]
  ))

(define hash0 (hash))
(define modls0 hash0)

;; read-p : S-exp -> Prog
(define read-p
  (match-lambda
    [`(,m ... (require ,reqs ...) ,e)
     (match-let ([modls (read-ms m modls0)])
       (PROG modls (read-e e '† modls reqs hash0)))]
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
           (MODL n decs (hash-set defs x (read-e e n ms reqs hash0)))]
          [(`(provide ,pr ...) (MODL n decs defs))
           (foldl (match-lambda**
                   [(`(,x ,c) (MODL n decs defs))
                    (MODL n (hash-set decs x (read-c c n ms reqs hash0)) defs)])
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
(define (read-e s [modl-name '†] [modls modls0] [reqs '()] [bound hash0])
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
    #|[`(and ,e) (loop e)]
    [`(and ,e ,e1 ...) (loop `(if ,e (and ,@ e1) #f))]
    [`(or ,e) (loop e)]
    [`(or ,e ,e1 ...) (let ([x (fresh-x e1)])
                        (loop `(let [,x ,e] (if x x (or ,@ e1)))))]|#
    [`(and ,e ...) (apply AND (map loop e))]
    [`(or ,e ...) (apply (curry OR modl-name) (map loop e))]
    [`(cond [else ,e]) (loop e)]
    [`(cond [,e1 ,e2] ,otherwise ...) (loop `(if ,e1 ,e2 (cond ,@ otherwise)))]
    
    ;; special forms
    [`(if ,e1 ,e2 ,e3) (IF (loop e1) (loop e2) (loop e3))]
    [`(μ (,x) ,e) (MU x (read-e e modl-name modls reqs (bind-vars bound `(,x))))]
    [`(mon ,lo ,l+ ,l- ,c ,e)
     (MON lo l+ l-
          (read-c c modl-name modls reqs bound)
          (loop e))]
    [`(λ (,x ... ,z ..) ,e)
     (if (and (symbol? z) (andmap symbol? x))
         (let ([params (append x (list z))])
           (LAM params
                (read-e e modl-name modls reqs (bind-vars bound params))
                #t))
         (error "Invalid var-λ variable declaration:" x z))]
    [`(λ (,x ...) ,e)
     (if (andmap symbol? x)
         (LAM x (read-e e modl-name modls reqs (bind-vars bound x)) #f)
         (error "Invalid λ variable declaration:" x))]
    
    ;; application
    [`(,f ,xs ...) (AP (loop f) (map loop xs) modl-name)]
    
    ;; variables / other values
    ['• (OPQ)]
    [x (cond
         [(symbol? x) (resolve-id modl-name modls reqs bound x)]
         [(base? x) x]
         [else (error "Invalid expression form:" x)])]))

;; S-exp Symbol [Hashtable Symbol Module] [Setof Symbol] [Setof Symbol] -> Contract
(define (read-c s [modl-name '†] [modls modls0] [reqs '()] [bound hash0])
  (define (loop x) (read-c x modl-name modls reqs bound))
  (match s
    [`(or/c ,c1 ,c2) (OR/C (loop c1) (loop c2))]
    [`(and/c ,c1 ,c2) (AND/C (loop c1) (loop c2))]
    [`(cons/c ,c1 ,c2) (STRUCT/C 'cons (list [loop c1] [loop c2]))]
    [`(struct/c ,t ,cs ...) (STRUCT/C t (map loop cs))]
    [`(,c1 ... ,c1′ .. ↦ (λ (,x ...) ,c2))
     (FUNC/C (map list x (append (map loop c1) (list (loop c1′))))
             (read-c c2 modl-name modls reqs (bind-vars bound x))
             #t)]
    [`(,c1 ... ↦ (λ (,x ...) ,c2))
     (FUNC/C (map list x (map loop c1))
             (read-c c2 modl-name modls reqs (bind-vars bound x))
             #f)]
    [`(,c1 ... ,c1′ .. ↦ ,c2) (let ([xs (fresh-xs (length `(,@ c1 ,c1′)) s)])
                                (loop `(,@ c1 ,c1′ ↦ (λ ,xs ,c2))))]
    [`(,c1 ... ↦ ,c2) (let ([xs (fresh-xs (length c1) c2)])
                        (loop `(,@ c1 ↦ (λ ,xs ,c2))))]
    [`(μ (,x) ,c) (MU/C x (read-c c modl-name modls reqs (hash-set bound x 'c)))]
    [x (if (and (symbol? x) (hash-has-pair? bound x 'c ))
           (REF/C x)
           (FLAT/C (read-e x modl-name modls reqs bound)))]))

(define (bind-vars bound xs)
  (foldl (λ (x b) (hash-set b x 'e)) bound xs))

;; hash-has-pair? : [Hashtable K V] K V -> Bool, (V ⊂ true?)
(define (hash-has-pair? h k v)
  (equal? v (hash-ref h k (λ () #f))))

;; Symbol Modules [Listof Symbol] [Setof Symbol] Symbol -> Exp
;; checks whether the identier can be found in any required module
(define (resolve-id from modls reqs bound name)
  (cond
    ; local variable
    [(hash-has-pair? bound name 'e) name]
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
         [else (match name
                 ['cons CONS]
                 ['cons? CONS?]
                 ['car CAR]
                 ['cdr CDR]
                 [x (∆ from x)])]))]))


;; returns fresh variable(s) not in given term
(define (fresh-x e)
  (variable-not-in e 'tmp))
(define (fresh-xs n e)
  (variables-not-in e (make-list n 'tmp)))
  

;; α-renames program
(define (α-rename-p′ p used0 maps)
  [match-define (PROG ms e) p]
  [define-values (ms1 used1) (α-rename-ms′ ms used0 maps)]
  [α-rename-e′ e used1])
;; α-renames modules
(define (α-rename-ms′ ms used0 maps)
  [define-values (ms1 used1) (ms used0)]
  [hash-for-each
   ms
   (λ (x m)
     (let-values ([(m′ used′) (α-rename-m′ m used1 maps)])
       (set! used1 used′)
       (set! ms1 (hash-set ms1 x m′))))]
  [values ms1 used1])
;; α-rename module
(define (α-rename-m′ m used0 maps)
  [match-define (MODL x cs es) m]
  [define-values (used1 cs1 es1) (used0 cs es)]
  [hash-for-each
   cs
   (λ (x c)
     (let-values ([(c′ used′) (α-rename-c′ c used1 maps)])
       (set! used1 used′)
       (set! cs1 (hash-set cs1 x c′))))]
  [hash-for-each
   es
   (λ (x e)
     (let-values ([(e′ used′) (α-rename-e′ e used1 maps)])
       (set! used1 used′)
       (set! es1 (hash-set es1 x e′))))]
  [values (MODL x cs1 es1) used1])
(define (α-rename-c′ c used0 maps)
  [define used1 used0]
  (match c
    [(FLAT/C e) (let-values ([(e′ used′) (α-rename-e′ e used1 maps)])
                  (values (FLAT/C e′) used′))]
    [(OR/C c1 c2) (let*-values ([(c1′ used2) (α-rename-c′ c1 used1 maps)]
                                [(c2′ used3) (α-rename-c′ c2 used2 maps)])
                    (values (OR/C c1′ c2′) used3))]
    [(AND/C c1 c2) (let*-values ([(c1′ used2) (α-rename-c′ c1 used1 maps)]
                                 [(c2′ used3) (α-rename-c′ c2 used2 maps)])
                     (values (AND/C c1′ c2′) used3))]
    [(STRUCT/C t cs)
     (values
      (STRUCT/C t
                (map (λ (c) (let-values ([(c′ used′) (α-rename-c′ c used1 maps)])
                              (set! used1 used′)
                              c′))
                     cs))
      used1)]
    [(FUNC/C `((,x ,c1) ...) c2 v?)
     (let* ([c1′ (map (λ (ci)
                        (let-values ([(ci′ used′) (α-rename-c′ ci used1 maps)])
                          (set! used1 used′)
                          ci′))
                      c1)]
            [zs (variables-not-in used1 x)]
            [maps′ (foldl (λ (x z m) (hash-set m x z)) maps x zs)])
       (let-values ([(c2′ used′ _) (α-rename-c′ c2 (append zs used1) maps′)])
         (values (FUNC/C (map list zs c1′) c2′) used′)))]
    [(MU/C x c)
     (let ([z (variable-not-in used1 x)])
       (let-values ([(c′ used′)
                     (α-rename-c′ c (cons z used1) (hash-set maps x z))])
         (values (MU/C z c′) used′)))]
    [(REF/C x) (values (REF/C (hash-ref maps x)) used1)]))
(define (α-rename-e′ e used0 maps)
  (define used1 used0)
  (match e
    [(AP f xs l)
     (let-values ([(f′ used′) (α-rename-e′ f used1 maps)])
       (set! used1 used′)
       (let ([zs (map (λ (x)
                        (let-values ([(x′ used′) (α-rename-e′ x used1 maps)])
                          (set! used1 used′)
                          x′))
                      xs)])
         (values (AP f′ zs l) used1)))]
    [(IF e1 e2 e3) (let*-values ([(e1′ used2) (α-rename-e′ e1 used1 maps)]
                                 [(e2′ used3) (α-rename-e′ e2 used2 maps)]
                                 [(e3′ used4) (α-rename-e′ e3 used3 maps)])
                     (values (IF e1′ e2′ e3′) used4))]
    [(MU x e1) (let ([z (variable-not-in used1 x)])
                 (let-values
                     ([(e1′ used′)
                       (α-rename-e′ e1 (cons z used1) (hash-set maps x z))])
                   (values (MU z e1′) used′)))]
    [(MON l0 l+ l- c e1)
     (let*-values ([(c′ used2) (α-rename-c′ c used1 maps)]
                   [(e1′ used3) (α-rename-e′ e1 used2 maps)])
       (values (MON l0 l+ l- c′ e1′) used3))]
    [(LAM xs e1 v?)
     (let ([zs (variables-not-in used1 xs)])
       (let-values ([(e1′ used′) (α-rename-e′ e1 (append zs used1)
                                              (foldl (λ (x z m) (hash-set m x z))
                                                     maps xs zs))])
         (values (LAM zs e1′ v?) used′)))]
    [(? symbol? x) (values (hash-ref maps x) used1)]
    [_ (values e used1)]))

(define (run f)
  (λ (x)
    (let-values ([(r _) (f x '() hash0)])
      r)))
(match-define
  `(,α-rename-p ,α-rename-e ,α-rename-c)
  (map run `(,α-rename-p′ ,α-rename-e′ ,α-rename-c′)))