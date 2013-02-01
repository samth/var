#lang scribble/lncs
@(require (only-in scribble/manual racketmod)
          slideshow/pict
          redex/pict
          scriblib/figure
          #;(only-in "lang-new.rkt" λrec ⇓))

@bold{Abstract}

Automated software verification is tricky, especially for programs
written in languages with first-class functions and control.
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
First-class functions and control worsen the situation even further
by making it too easy to assume spurious paths.
Tobin-Hochstadt and Van Horn (2012) make a novel approach of using symbolic execution
with @emph{specifications as values}, which is mostly orthogonal
to a language's semantics
and readily scales to an expressive set of language features.
But contracts, being boundary-level specifications, turn out not sufficient
for giving precise analyses in quite a few cases.
If a value is not guarded by the right contract when it flows into a module,
there may not be enough information to verify the value that flows back out.
In the following example, their analysis relies on an appropriate disjunctive contract
to monitor the argument.
When an opaque value is refined by this contract, it splits into more precise values.
This splitting, in many cases, coincides with the test in the function's body
and helps verification.
@verbatim[#:indent 4]{
                      
(module
  (provide
   [maybe-head ((μ (l) (or/c nil (cons/c any/c l))) →
                   (or/c #f (cons/c any/c nil)))])
  (define (maybe-head x)
    (if (cons? x) (cons (car x) nil) #f)))
    
}
However, this module, with a simpler contract, cannot be verified:
@verbatim[#:indent 4]{
                      
(module
  (provide
   [maybe-head (any/c → (or/c #f (cons/c any/c nil)))])
  (define (maybe-head x)
    (if (cons? x) (cons (car x) nil) #f)))
    
}

[TODO:
Is the purpose of the old analysis just to prove that a module
respects its own contract and it doesn't matter if it violates others'
(like ∆, the language, in this case)?
If it's ok for the module to violate ∆, i will need to complicate this example
a bit by using dependent contract to make the old analysis return a false blame)
, like this:
@verbatim[#:indent 4]{
(any/c → (λ (x) (flat (λ (y) (if (cons? x) (cons? y) (false? y))))))
}
]

Ad-hoc rules remembering primitive tests do not suffice,
because real programs can have complex and abstracted tests
on arbitrary expressions that imply valuable facts when they fail or pass.
For example, the following expression should return a number
and never cause an error regardless of what values @tt{x} and @tt{y}
have at run-time.

[Example 14 from Sam's, slightly modified]
@verbatim[#:indent 4]{
                      
(if (and (or (num? x) (str? x)) (cons? y))
    (cond
      [(and (num? x) (num? (car y))) (+ x (car y))]
      [(num? (car y)) (+ (str-len x) (car y))]
      [else 0])
    0)

}

This problem has been solved in [Sam's paper] in the context of
type-checking.
We want to employ these ideas in symbolic execution to strengthen
our previous analysis.

Contribution:
@itemlist[
  @item{We give a method of significantly improving precision for
        symbolic execution by taking advantage of program flow}
  @item{We show that the new analysis can verify a larger set of programs}
  @item{We discuss useful by-products coming out of this analysis, namely 
        more elimination of run-time checks and dead-code,
        and analyzing function's preconditions}
]

Plan:
@itemlist[
  @item{High-level description}
  @item{Simple language without •}
  @item{Add • to language}
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

@section{Adding Abstract Values}

@section{Discussion}

@section{Related Work}

@section{Conclusion}



