#lang scribble/lncs
@(require (only-in scribble/manual racketmod)
          slideshow/pict
          redex/pict
          scriblib/figure
          #;(only-in "lang-new.rkt" λrec ⇓))

@section{Introduction}

Verifying programs written in untyped languages has always been tricky
because the validity of partial functions usage heavily depends on program flow.

Taking contracts into account gives opportunities for a more precise analysis,
but this turns out not enough in practice and neccessitates a more general
solution to deal with common programming patterns.

In particular, the old analysis relies on a function's argument being monitored
by some appropriate disjunctive contract that coincides with the tests
in the function's body.
Then when an opaque value is refined by this disjunctive contract,
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

Simple, ad-hoc rules remembering primitive tests on variables
do not suffice, because real programs can have a complex and abstracted tests
on arbitrary expressions that imply valuable facts about variables
when fail or pass.
For example, the following expression should return a number
regardless of what value @tt{x} and @tt{y} receive at run-time:

[Example: from Sam's, slightly changed]
@verbatim[#:indent 4]{
                      
(let [x •]
  (if (or (num? x) (str? x))
      (let [y (cons • •)]
        (cond
          [(and (num? x) (num? (car y))) (+ x (car y))]
          [(num? (car y)) (+ (str-len x) (car y))]
          [else 0]))
      0))

}

This problem has been solved in [Sam's paper] in the context of
type-checking.
We want to employ these ideas in symbolic execution to strengthen
our previous analysis.

Contribution:
@itemlist[
  @item{We give a method of significantly improving precision for symbolic execution,
        taking advantage of the common patterns in untyped languages.}
  @item{}
]

Plan:
@itemlist[
  @item{High-level description}
  @item{Language without contracts}
  @item{Add contracts to language}
]

@section{Overview}
The analysis mimicks a programmer's intuitive reasoning about unknown values.
We use symbolic execution as a systematic way of automating these intuitions.
Appropriate portions of the environment are refined after every primitive application.
By maintaining an environment that keeps track of what we have learned so far
and threading it through every execution step,
we retain information despite arbitrarily deep layers of abstraction and
complex test combinations.


@section{Simple Language}

@section{Adding Contracts}
