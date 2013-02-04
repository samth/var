#lang scribble/lncs
@(require (only-in scribble/manual racketmod)
          slideshow/pict
          redex/pict
          scriblib/figure
          (only-in "lang-paper-simple.rkt"
                   λrec [render-⇓ render-⇓-s] [render-APP render-APP-s])
          (only-in "lang-paper.rkt" sλrec render-⇓ render-APP))

@bold{Abstract}

Automated software verification is tricky, especially in the presence
of higher-order functions.
@emph{[... TODO: Why it's an interesting problem..]}
We present a solution based on symbolic execution that reasons about
unknown program portions effectively and scales to many language features.
What comes out of this analysis is a powerful tool
for verifying software correctness, justifying elimination of run-time checks
and dead-code, and answering questions of the form
"What are neccessary conditions for this function's input such that
its output has property X?".

@section{Introduction}

Modular reasoning about software is hard because the analysis
needs to allow an arbitrary number of unknown portions and make conservative assumptions.
First-class functions worsen the situation further
by making it too easy to assume spurious paths.
Tobin-Hochstadt and Van Horn (2012) make a novel approach of
using symbolic execution with @emph{specifications as symbolic values},
which readily scales to an expressive set of language features.
But contracts, being boundary-level specifications, turn out not enough
for giving precise analyses in quite a few cases.
The analysis from this paper does a good job reasoning about programs when invariants
are encoded as contracts, but not when these same invariants are encoded
in the program logic itself.
For example, although the following two function definitions
are roughly equivalent, the analysis can only verify the first one:

@verbatim[#:indent 4]{

double : number? → number?
(define (double x)
  (* x 2))

}

@verbatim[#:indent 4]{
                      
double : any? → number?
(define (double x)
  (if (number? x) (* 2 x) (error "Not a number")))
                      
}

In the second definition,
the analysis cannot verify that the multiplication is always applied
to two numbers because it is insensitive to ordinary tests.
This neccessitates a more general solution that infers information more effectively from the program logic.
Ad-hoc rules remembering simple tests do not suffice,
because real programs can have complex and abstracted tests
on arbitrary expressions that imply valuable facts when they fail or pass.
For example, the following expression should return a number
and never cause an error regardless of what values @tt{x} and @tt{y}
have at run-time:

[Example 14 from Sam's, slightly modified]
@verbatim[#:indent 4]{
                      
(if (and (or (num? x) (str? x)) (cons? y))
    (cond
      [(and (num? x) (zero? x)) 0]
      [(and (num? x) (num? (car y))) (/ (car y) x)]
      [(num? (car y)) (+ (str-len x) (car y))]
      [else 0])
    0)

}

This problem has been solved in [Sam's paper] in the context of
type-checking.
We want to employ these ideas in our new analysis and aim
for a stronger property:
If type-checking only proves the absence of certain classes of bugs,
our analysis tries to prove that a program is free from run-time errors
and is correct up to the specifications enforced by contracts.

We make the following contributions:
@itemlist[
  @item{We give a method of significantly improving precision for
        symbolic execution by making better use of tests and program flow.}
  @item{We show how the new analysis is used to verify that a module
        cannot be blamed.
        When the analysis cannot prove the absence of blames,
        there is enough information for programmers to inspect.
        This also gives insights into improving the analysis
        when the blame is false.}
  @item{We discuss other useful by-products of this analysis, namely 
        more elimination of run-time checks and dead-code,
        and analyzing function's preconditions.}
]

Plan:
@itemlist[
  @item{High-level description}
  @item{Simple language without •}
  @item{Add • to language}
  @item{Application to contract verification}
  @item{Discussion: evaluate results, by-products, possible improvements}
  @item{Related work}
]

@section{Overview}
The analysis mimicks a programmer's intuitive reasoning about unknown values.
We use symbolic execution as a systematic way of automating these intuitions.
Appropriate portions of the environment are refined after every primitive application.
We try to utilize these refinements to avoid spurious results.
When ambiguity occurs, we assume both branches and remember our decision in each.
By maintaining an environment that keeps track of what we have learned so far
and threading it through every execution step,
we retain information despite arbitrarily deep layers of abstraction and
complex test combinations.

@section{Simple Language}
@subsection{Syntax}

(TODO: We cut μ a while ago because it was weird to use substitution when
we already had an environment.

Can we use named function, something like @tt{(rec [f x] e)} ?)

@(centered (parameterize
               ([render-language-nts '(e a v b o o1 o2 n s p? acc ρ V A)])
             (render-language λrec)))

@subsection{Semantics}
(Standard)
@subsubsection{Evaluation}
@tt{ρ ⊢ e ⇓ A}
@(centered (render-⇓-s))
@subsubsection{Application}
@(centered (render-APP-s))

@section{Adding Abstract Values}
@subsection{Syntax}
@itemlist[
  @item{@tt{•} stands for an opaque piece of value syntax}
  @item{@tt{★} is an opaque, refinable closed value}
  @item{@tt{l} is a label as an alias for some opaque value}
]

@(centered (parameterize ([render-language-nts '(v V σ)])
             (render-language sλrec)))
@subsection{Semantics}
@subsubsection{Evaluation}

@tt{σ, ρ ⊢ e ⇓ A; σ′}

means expression @tt{e}, closed by @tt{ρ}, under refinements @tt{σ}
for opaque values, evaluates to @tt{A}
and results in a set of refinements @tt{σ′} more precise than
or the same as @tt{σ}.
@(centered (render-⇓))
@subsubsection{Application}

[TODO:
I throw in ★ and ERR for havoc for now due to lack of recursion.
]

@(centered (render-APP))

@section{Discussion}
@subsection{Result Evaluation}
@subsection{By-products}
@subsection{Future Improvements}

@section{Related Work}

@section{Conclusion}

