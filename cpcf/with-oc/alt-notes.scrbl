#lang scribble/lncs
@(require (only-in scribble/manual racketmod)
          slideshow/pict
          redex/pict
          "alt.rkt"
          scriblib/figure)

This is an attempt to get around problems from treating @tt{mon}-expression
as a special language construct at run-time:
@itemlist[
  @item{@tt{Γ}'s domain needed maintenance at multiple places.
        It was not obvious to me how to make the rules less awkward.}
  @item{The machine was complicated to implement.
        A few ad-hoc continuation frames were needed for disjunctive and pair
        contracts.
        Also, the current rule for applying wrapped functions would not support
        stateful contracts for monitoring callbacks mentioned in 2.5 Findler-Felleisen.
        (In my implementation, the contract's range component was evaluated after
        instead of before function application.)
        It was not obvious to me how to fix this without inventing a new type of continuation frame.}
  @item{There were 2 mechanisms to refine abstract values: contracts and propositions.
        Contracts were more expressive but local (they refined specific values).
        Propositions only involved primitive predicates but had more wide-spread
        effects (facts discovered in one place could be used for several variables
        and derived paths).
        In fact, @tt{Γ} could be improved to store propositions on module references.
        This is also an attempt to unify these two mechanisms for remembering facts.}
]

@section{Source language}
Our usual language with @tt{mon}-expressions:

@(centered (parameterize ([render-language-nts '(e a v b o1 o2 op p? c)])
             (render-language scpcf-src)))

@section{Target language}
The target language does not allow @tt{mon} expressions,
and have a @tt{refine} expression for explicitly refining a value with a predicate.

@(centered (parameterize ([render-language-nts '(e)])
             (render-language scpcf)))

Translation from source to target language is done through the @tt{compile} metafunction.
It distributes with most constructs, and turns @tt{mon}-expressions into explicit tests,
blames and refinements using @tt{MON}.

@verbatim[#:indent 4]{
compile : e_source -> e_target
}
@(render-metafunction compile)

(The first 3 rules for @tt{MON} are just to reduce cluttering.
@tt{MON-1} is like @tt{MON} but does not generate a temporary variable to hold result.)

@verbatim[#:indent 4]{
MON : c e -> e
}
@(render-metafunction MON)

Here are some example results:
@verbatim[#:indent 4]{
                      
(mon (μ (list?)
        (or/c (flat nil?)
              (cons/c (flat tt) list?)))
     x)

translates to:
     
((μ (list?)
      (λ (A)
        (let (P? nil?)
          (if (P? A)
              (refine A P?)
              (if (cons? A)
                  (cons
                   (let (A1 (car A)) (if (tt A1) (refine A1 tt) blame))
                   (list? (cdr A)))
                  blame)))))
   x)
}, and
@verbatim[#:indent 4]{
                      
(mon ((flat int?) ↦ (λ (x) (flat (λ (y) (equal? x y)))))
     (λ (z) z))
              
translates to:

(if (proc? (λ (z) z))
    (λ (x)
      (let (P? (λ (y) (equal? x y)))
        (let (A ((λ (z) z) (if (int? x) (refine x int?) blame)))
          (if (P? A) (refine A P?) blame))))
    blame)
    
}.
 
@subsection{Proposition environment}
@tt{Γ} now maps from paths to (potentially) arbitrary propositions.
The grammar for @tt{Γ} and @tt{φ} is now:

@(centered (parameterize ([render-language-nts '(Γ φ P? o′ acc)])
             (render-language scpcf)))

Specifically:
@itemlist[
  @item{@tt{o′ ↦ P?} means applying predicate @tt{P?} to @tt{ρ[o′]}
       will produce a @tt{non-#f} value.}
  @item{@tt{o′ ↦ (¬ P?)} means applying predicate @tt{P?} to @tt{ρ[o′]}
       will produce @tt{#f}.}
  @item{@tt{o′ ↦ (Cons φ_1 φ_2)} means @tt{ρ[o′]} is a pair and @tt{φ_1}
       holds for @tt{car(ρ[o′])}, @tt{φ_2} holds for @tt{cdr(ρ[o′])},
       recursively.}
  @item{@tt{o′ ↦ (φ_x → φ_y)} means @tt{ρ[o′]} is a function that when
       applied to a value that satisfies @tt{φ_x}, will return
       a value that satisfies @tt{φ_y}.}
], where path lookup in @tt{ρ} is defined as
@verbatim[#:indent 4]{
ρ[(x)] = ρ[x] (with regular definition of variable lookup)
ρ[(acc_1 acc_2 ... x)] = acc_1(ρ[(acc_2 ... x)])
}

@section{Big-step semantics for target language}

The rules are straight forward and familiar apart from one for @tt{refine}-expression.

@subsection{Value}
@(centered (parameterize ([judgment-form-cases '("val")])
             (render-judgment-form ⇓)))
@subsection{Variable}
@(centered (parameterize ([judgment-form-cases '("var")])
             (render-judgment-form ⇓)))
@subsection{Application}
@(centered (parameterize ([judgment-form-cases '("app1" "app2")])
             (render-judgment-form ⇓)))
@(centered (parameterize ([judgment-form-cases '("app-err1" "app-err2" "app-err3")])
             (render-judgment-form ⇓)))
@subsection{Conditional}
@(centered (parameterize ([judgment-form-cases '("if-true" "if-false" "if-err")])
             (render-judgment-form ⇓)))
@subsection{Refining} (The only new rule)
@(centered (parameterize ([judgment-form-cases '("refine")])
             (render-judgment-form ⇓)))
@subsection{Rec}
@(centered (parameterize ([judgment-form-cases '("μ")])
             (render-judgment-form ⇓)))
@subsection{Blame}
@(centered (parameterize ([judgment-form-cases '("blame")])
             (render-judgment-form ⇓)))

@subsection{Closure application}
@(centered (parameterize ([judgment-form-cases '("app-λ" "app-o1" "app-o2")])
             (render-judgment-form ⇓a)))

@section{Target language's machine semantics}
(Should be mostly standard andn familiar with no ad-hoc frames for monitoring
disjunctive/pair contracts...)

@section{Appendix: other metafunctions}

@subsection{@tt{Γ-flush : Γ ρ -> ρ}}
@(render-metafunction Γ-flush)

@subsection{@tt{Γ-refine : V Γ o′ -> V}}
@(render-metafunction Γ-refine)

@subsection{@tt{REFINE : V φ -> V}}
@(render-metafunction REFINE)
                      
@subsection{@tt{mk-φ : (acc ...) φ -> φ}}
@(render-metafunction mk-φ)

@subsection{@tt{close : v ρ O -> V}}
@(render-metafunction close)