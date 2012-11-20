#lang scribble/lncs
@(require (only-in scribble/manual racketmod)
          slideshow/pict
          redex/pict
          "lang.rkt"
          "machine.rkt"
          "judgment.rkt"
          scriblib/figure)

@section{Previously problematic programs}

Basically programs not guided by appropriate disjunctive contracts.
@verbatim[#:indent 4]{
                      
(module
 (provide [f (any/c ↦ any/c)])
 (define (f x)
   (if (cons? x) (car x) x)))
   
}
Another example is the expression generated by @tt{FC(cons/c c1 c2)} in the paper.
@verbatim[#:indent 4]{
                      
(FC (C1 C2)) = (λ (y) (and (cons? y)
                           ((FC C1) (car y))
                           ((FC C2) (cdr y))))
                           
}
Further, testing a compound expression doesn't give information about the
constituent variable. See this @tt{lastpair} example from the Wright paper
@verbatim[#:indent 4]{

; cons? → cons?
(λ (s)
  (if (cons? (cdr s))
      (lastpair (cdr s))
      s))
      
}

@section{Language}

Untyped λ-calculus augmented with
@itemlist[
  @item{contracts}
  @item{abstract values refinable by contracts}
  @item{syntactic sugar for @tt{cond}, @tt{and}, @tt{or}, @tt{let}, and @tt{begin}}
]
Labels are omitted for @tt{mon} and @tt{blame}.

@(centered (parameterize ([render-language-nts '(e a v op o1 o2 p? ψ c ρ O Γ o o′ acc C V CC)])
             (render-language scpcf)))

There is no explicit representation for union types.
Instead, non-determinism is used for better precision.
One example to illustrate this is from the Chugh paper.
Instead of returning @tt{(∪ int? bool?)},
this function returns an @tt{int?} or @tt{bool?}
in different non-deterministic branches.

@verbatim[#:indent 4]{
(λ (x)
  (cond
    [(int? x) (- 0 x)]
    [(bool? x) (false? x)])
}

Γ is the proposition environment, mapping each path to a set of predicates.

@verbatim[#:indent 4]{
[o ↦ ψ1 ψ2 ...]
}
means
@verbatim[#:indent 4]{
(ψ1(o) ∧ ψ2(o) ∧ ...)
}.

@section{Big-step semantics}

@verbatim[#:indent 4]{
Γ ⊢ C ⇓ V; Γ′; o
}
means under assumptions @tt{Γ}, closure @tt{C} evaluates to @tt{V}, resulting in new set of propositions @tt{Γ′} that have to hold.

Invariants:
@itemlist[
  @item{@tt{Γ}, @tt{C} and @tt{Γ′} have the same domain.
        (The metafunction @tt{dom} is also conveniently 'overloaded'
        on closures (partially), discussed later).}
  @item{@tt{dom(C)[o]} is @tt{V}, if @tt{dom(C)} is defined}
  @item{@tt{Γ′[o]} doesn't give further information that's not already in @tt{V}}
]

@subsection{Value}
Closed value @tt{V} evaluates to itself, probably with all interesting propositions
from @tt{Γ} flushed in.

@(centered (parameterize ([judgment-form-cases '("val")])
             (render-judgment-form ⇓)))

@tt{flush} converts all relevant propositions from @tt{Γ} into contracts to refine
free variables in @tt{V}'s environment. The following example illustrates why this
is helpful. This expression should always returns @tt{#t}
@verbatim[#:indent 4]{
(int? [(let [x •]
         (if (int? x)
             (λ (_) x)
             (λ (_) 1)))
       •])
}
By the time the @tt{(let ...)} part is
done, all propositions about @tt{x} will have already been 'popped' out.
We need a way to remember that @tt{x} is an @tt{int?} in @tt{(λ (_) x)}.
This was not a problem with type-checking because we could look through @tt{λ}
and state it was of type @tt{(any? → int?)}.

@subsection{Variable}

@subsection{Application}

@subsubsection{λ-abstraction}

@subsubsection{Monitored function}

@subsubsection{Primitive operation}

@subsection{Conditional}

@subsection{Monitored expression}

@section{Machine semantics}

Machine state
@(parameterize ([render-language-nts '(ς)])
   (render-language scpcf-m))

@(render-reduction-relation red #:style 'compact-vertical)

@section{Appendix: metafunctions}

@subsection{Evaluation based on big-step semantics}

This is not really readable because I escaped to Racket to
define convenient syntax to handle non-determinism that automatically
propagated errors and removed duplicates. For example:
@verbatim{
(non-det:
  [V′ Γ′ o ← (step Γ C)]
  [...])
}
means closure @tt{C} under @tt{Γ} non-deterministically evaluates to
@tt{(V′ Γ′ o)}, then stuff in @tt{[...]} are performed separately
for each branch (if there's more than 1).

The first 12 rules are just for syntactic sugar.

@verbatim{
step : Γ C -> {A ...} , where A ::= (V Γ o)
                                  | ERR
}
@(render-metafunction step)

@subsection{Proposition environment manipulation}

@verbatim{
push : Γ x -> Γ
resets all propositions refering to x
e.g. (push ([(car x) ↦ str?] [z ↦ int?]) x) → ([x ↦ tt] [z ↦ int?])
}

@verbatim{
pop : Γ x -> Γ
removes x from environment's domain
e.g. (pop ([(car x) ↦ str?] [z ↦ int?]) x) → ([z ↦ int?])
}

@verbatim{
mk-Γ : {X ...} Γ -> Γ
makes environment with given domain and join with Γ
e.g. (mk-Γ {x} ([x ↦ cons?] [(car x) ↦ str?] [z ↦ int?]))
     → ([x ↦ cons?] [(car x) ↦ str?])
}

@verbatim{
upd-Γ : Γ Γ -> Γ
uses 2nd environment to refine 1st one in their common domain
}