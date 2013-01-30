#lang scribble/lncs
@(require (only-in scribble/manual racketmod)
          slideshow/pict
          redex/pict
          scriblib/figure)

@section{Introduction}

Verifying programs written in untyped languages has always been tricky
due to the fact that the validity of partial functions usage heavily
depends on program flow.

Taking contracts into account results in opportunities for more precise analyses,
but this turns out not enough in practice and neccessitates a more general
solution to deal with common programming patterns.

In particular, the old analysis relied the argument being monitored
by some appropriate disjunctive contract that conincided with the tests
in the function's body.
When an opaque value is refined by this disjunctive contract,
it splits accordingly.

For example, the following module is justified:
@verbatim[#:indent 4]{
                      
(module
  (provide
   [maybe-head ((μ (l) (cons/c nil (cons/c any/c l))) →
                   (or/c #f (cons/c any nil)))])
  (define (maybe-head x)
    (if (cons? x) (cons (car x) nil) #f)))
    
}
But this one, with a simpler contract, is not:
@verbatim[#:indent 4]{
                      
(module
  (provide
   [maybe-head (any/c → (or/c #f (cons/c any nil)))])
  (define (maybe-head x)
    (if (cons? x) (cons (car x) nil) #f)))
    
}

Simple, ad-hoc rules for remembering primitive tests on variables
do not suffice, because real programs can have complex, abstracted tests
on a complex expression that implies facts about variables when the
tests fail or pass.

[Example: one from Sam's or Wright's paper]

This problem has been solved in [Sam's paper] in the context of
type-checking.
We want to employ these ideas in symbolic execution to strengthen
the old analysis.

Plan:
@itemlist[
  @item{High-lever description}
  @item{Language without contracts}
  @item{Add contracts to language}
]

@section{Overview}

@section{Simple Language}

@section{Adding Contracts}
