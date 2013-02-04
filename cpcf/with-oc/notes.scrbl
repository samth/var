#lang scribble/lncs
@(require (only-in scribble/manual racketmod)
          slideshow/pict
          redex/pict
          "lang1.rkt"
          scriblib/figure)

This notes summarizes problems we're having and maybe semi-solutions
so far.

@section{Recursion}
We had @tt{μ} before but cut that out because we used an environment
and it was weird to use substitution.
If we don't have modules yet,
can we use named function for recursion instead? (needed for @tt{havoc})

@section{Compiling away contracts}
David and I thought about compiling away contracts and let the new
mechanism subsume the task of remembering refinements.

It turns out this is not quite possible yet.
The new mechanism is good at remembering consequences
of applying primitive operators, but it cannot easily
scale to remember more complex constrained, like these:
@verbatim[#:indent 4]{
                      
(define (even? x)
  (= (mod x 2) 0))

(define (ok-password-length? s)
  (<= (string-length x) 30))

}

@tt{σ} can at best be generalized to remember relations
like @tt{mod x 2 = 0}, but I'm afraid this solution
will not scale well.

I think the appropriate thing to do is either
adding back all the contract stuff,
or accept a hybrid solution of adding 1 special
construct that explicitly memoizes
a function application.
This way we remember all properties expressed in primitive ops
as well as the complex ones enforced explicitly by programmers.

@section{Non-termination}

@subsection{Tail-recursion}

If a state @tt{<e, ρ, σ, k>} transitions to @tt{<e, ρ′, σ′, k>}
(same expression and stack, with probably different environment and store),
can we approximate it by using an environment @tt{ρ′′} that approximates
both @tt{ρ} and @tt{ρ′}?

@subsection{Non-tail recursion}

@subsubsection{When there's a contract}

Previously we approximated a non-tail recursive function by its contract.
This worked perfectly when the function was applied to @tt{•},
which was more abstract than any other values.

It turns out we need to be careful to make sure that
the new argument is more precise than or the same as the old one.
For example, consider the following function:

@verbatim[#:indent 4]{
                      
(f : number? → number?
(define (f x)
  (if (zero? x) "string" (add1 (f (sub1 x)))))
                      
}

If the function is applied to @tt{(• positive?)},
we won't discover the blame, even though
any concretization of @tt{(• positive?)} will make
this function fail.
The problem is if we had some fancy range-remembering,
then this could go on forever,
say @tt{(f [1, ∞))} calls @tt{(f [0, ∞])},
which calls @tt{(f [-1, ∞])}, and so on.
So we'll need some form of widening.

But I'm not sure if this situation will really come up
in a real execution,
because when havoc-ing a function, we apply it to @tt{•}.

@subsubsection{When there's no contract}
I think if there's a way to observe this pattern efficiently,
we can have a better apprimation of a recursive function 
that doesn't come with a contract:

When it's the case that:
@itemlist[
  @item{@tt{<e, ρ, k>} transitions to @tt{<k, V_i>}, there may be several of these.}
  @item{@tt{<e, ρ, k>} transitions to @tt{<e, ρ′, Ki k>} (same expression, strictly bigger stack)}
  @item{We have discovered all possible blames elsewhere}
]

We conclude that the result can be approximated to:

@tt{<k, V>}

, where @tt{V} is something like

@tt{(μ (x) (∪ V_i ... (Ki x) ...)}.

For example, with factorial, where the only base case is @tt{1}
and the pending application is @tt{(* n)},
we conclude its result is

@tt{(μ (x) (∪ 1 (* (• number?) x)))}

And if we assume all possible errors have been discovered elsewhere,
we can take the range of @tt{*}, which is @tt{number?},
and conclude that @tt{factorial}'s result is @tt{(• number?)}.

If this works, it should scale to other functions
on recursive data like binary trees as well,
and is something we can resort to when we don't
have a contract.