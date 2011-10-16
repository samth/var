#lang var ;trace
#|
  REVIEWER WRITES:

  As I understand it, if you pass a function with a non-trivial contract
  off to opaque code, you will definitely get a blame from the demonic
  context, thereby rendering it a little too pathological. Suppose I have a
  missing module

    foo with contract: ((Nat -> Nat) -> Nat)

  now consider the expression
        
    foo add1

  where add1 has the contract Nat -> Nat.

  Now, as I understand the DEMONIC reduction rule on p6. One of the possible
  outcomes of the above is that

    foo add1 → …(add1 \hole) ...

  because of the y (x \hole) outcome. Now the above (add1 \hole) is going to
  throw a blame. This is odd, as “foo”’s contract says that it promises to
  call its input with only Nat values (and expects Nat as output). Shouldn’t
  you constrain the \hole above with the contract of foo? What am I missing?
 
WE RESPONDED:

  We can run this program in our tool.  The program is:

  (module foo ((nat? -> nat?) -> nat?) ●)
  (module addone (nat? -> nat?) (λ (n) (add1 n)))

  The results are:

    > (foo addone)
    '(● nat?)
    '(blame foo foo (●) nat? (●))

  as we would want, since `foo' might not meet its contract, but
  otherwise we get back a `nat?'.  We get this result precisely because
  the \hole is constrained by `nat?' when it passes through the contract
  of `foo'.  This is seen in the first rule under "Remembering
  contracts", on page 6 of the paper, since U = V/{C}, thus remembering
  C, in this case `nat?'.
|#

(module foo racket 
  (provide/contract [foo (-> (-> nat? nat?) nat?)]))

(module addone racket 
  (require) 
  (define (addone n) (add1 n)) 
  (provide/contract [addone (-> nat? nat?)]))

(require (only-in foo foo) (only-in addone addone))
(foo addone)