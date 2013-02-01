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
First-class functions worsen the situation even further
by making it too easy to assume spurious paths.
Tobin-Hochstadt and Van Horn (2012) make a novel approach of using symbolic execution
with @emph{specifications as symbolic values}, which is mostly orthogonal
to a language's semantics
and readily scales to an expressive set of language features.
But contracts, being boundary-level specifications, turn out not sufficient
for giving precise analyses in quite a few cases.
The analysis in the paper does a good job reasoning about programs when invariants
are encoded as contracts, but not when they are encoded in the program logic itself.
This neccessitates a more general solution that learns about the program
more effecitvely.
If the analysis does a good enough job of exploring facts through tests
and program flow, this implies that contracts can be compiled into
this smaller language and have invariants checked by this new analysis.

The following example...
@verbatim[#:indent 4]{
                      
(provide
 (f (even? → even?))
 (define (f x)
   (+ 2 x)))
                      
}

@verbatim[#:indent 4]{
                      
(provide
 (f (number? → even?))
 (define (f x)
   (if (even? x) (+ 2 x) (error "input not even"))))
   
}


Ad-hoc rules remembering simple tests do not suffice,
because real programs can have complex and abstracted tests
on arbitrary expressions that imply valuable facts when they fail or pass.
For example, the following expression should return a number
and never cause an error regardless of what values @tt{x} and @tt{y}
have at run-time.

[Example 14 from Sam's, slightly modified]
@verbatim[#:indent 4]{
                      
(if (and (or (num? x) (str? x)) (cons? y))
    (cond
      [(and (positive? x) (num? (car y))) (/ (car y) x)]
      [(num? (car y)) (+ (str-len x) (car y))]
      [else 0])
    0)

}

This problem has been solved in [Sam's paper] in the context of
type-checking.
We want to employ these ideas in symbolic execution to strengthen
our previous analysis.
While type-checking only rules out certain types of errors,
we aim for a stronger property: That the execution reports no error
implies the absence of runtime errors for all concretization of
program inputs.

Contribution:
@itemlist[
  @item{We give a method of significantly improving precision for
        symbolic execution by making better use of tests and program flow}
  @item{We show that the new analysis can verify a larger set of programs
        , proving that they are free of run-time errors.
        In case of errors, the analysis provides enough information
        for programmers to inspect and see whether the errors can actually
        happen at run-time or not.}
  @item{We discuss useful by-products coming out of this analysis, namely 
        more elimination of run-time checks and dead-code,
        and analyzing function's preconditions}
]

Plan:
@itemlist[
  @item{High-level description}
  @item{Simple language without •}
  @item{Add • to language}
  @item{Apply this to handle contracts}
  @item{Discussion: evaluate results, by-products, possible improvements}
  @item{Related work}
]

@section{Overview}
The analysis mimicks a programmer's intuitive reasoning about unknown values.
We use symbolic execution as a systematic way of automating these intuitions.
Appropriate portions of the environment are refined after every primitive application.

Compared to type-checking, symbolic execution makes the process of reasoning simpler
and more transparent.
Instead of saying "If this is true, then that is true", we think of it as either
"We know it's true", "We know it's not true", or "We don't know, let's split and remember".

By maintaining an environment that keeps track of what we have learned so far
and threading it through every execution step,
we retain information despite arbitrarily deep layers of abstraction and
complex test combinations.

@section{Simple Language}
@subsection{Syntax}
@(centered (parameterize
               ([render-language-nts '(e a v b o o1 o2 n s p? acc ρ V A)])
             (render-language λrec)))
@subsection{Semantics}
The language's semantics is mostly standard.
@subsubsection{Evaluation}
@(centered (render-⇓-s))
@subsubsection{Application}
@(centered (render-APP-s))

@section{Adding Abstract Values}
@subsection{Syntax}
@(centered (parameterize ([render-language-nts '(v V)])
             (render-language sλrec)))
@subsection{Semantics}
@subsubsection{Evaluation}
@(centered (render-⇓))
@subsubsection{Application}
@(centered (render-APP))

@section{Discussion}
@subsection{Interesting programs verified}
@subsection{Applications}
@subsubsection{Inferring neccessary conditions}
@subsubsection{Optimization}
@subsection{Improvements}

@section{Related Work}
@subsection{Symbolic Execution}
@subsection{Contract Verification}
@subsection{Occurence Typing}

@section{Conclusion}



