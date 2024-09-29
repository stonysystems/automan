# Summary

The following templates guarantee an exact semantics between certain universal
quantifications (forall) involving sequences and maps in the protocol
specification and the generated sequence and map comprehensions in the
implementation. The key idea is to treat the domain and the mapping/tabulation
of collections as pseudo-fields: for both sequences and maps, one boolean
expression template (in the case of map, also a quantification) precisely
determines the domain `Dom`, and another determines the mapping `f: Dom -> Cod**.

**Convention:** `backticks` marks mathematical / non-Dafny notation, whereas

    text proceded by newline and 4 spaces

is Dafny code (with \<text inside angle brackets\> denoting a metavariable)

## Sequences

The domain for a sequence `s` is always of the form `Dom = {0 ... n-1}` for some `n`
(i.e., `n` is precisely `|s|`). When `s` is a (member-qualified) output
variable, the template we look for is

    |s| == \<numeric_expression\>

which determines `n` and thus `Dom`.

The mapping function `f` is determined by assuming an arbirary element `idx` of
the domain, i.e., `idx in {0 .. n-1}`, and determining the value of `f(idx)`.
The templates for this (for output variable `s`) are as follows:

    forall idx | 0 <= idx < |s| :: s[idx] == \<expr\>
    forall idx :: 0 <= idx < |s| ==> s[idx] == \<expr\>

in lib/moder.ml, this is represented by the constructor QFVarRange

## Maps

The domain for a map `m` is a finite subset of the type of keys, e.g. for

    type Votes = mape<OperationNumber, Vote>

and `m : Votes`, the domain of `m` is a finite set of integers. The template for
this is

    forall key :: key in m <==> \<boolean_expression\>

which is to say, we are looking for the necessary and sufficient conditions to
determine that `key` is in `Dom`. For example, in
Protocol/RSL/Acceptor.i.dfy::LAddVoteAndRemoveOldOnes we have

    forall opn :: opn in votes' <==> opn >= log_truncation_point && (opn in votes || opn == new_opn)

meanwhile, in RemoveVotesBeforeLogTruncationPoint, the second and third conjunct
can be replaced with

    forall opn :: opn in votes' <==> opn in votes && opn >= log_truncation_point

without changing the semantics of the original predicate

- **Aside:** The justification is:
  - `forall opn :: opn in votes' ==> opn >= log_truncation_point` by the
    contrapositive of the 2nd
  - by the first, `forall opn :: opn in votes' ==> opn in votes`, so we can obtain
    `forall opn :: opn in votes' ==> opn in votes && opn >= log_truncation_point`
  - take the above and the 3rd to obtain the equivalence

The mapping function `f` is (again) determined by assuming an arbitrary elemeny
`key` of the domain and determining the value of `f(key)`.
The templates for this (for output variable `m`) are as follows.

    forall key <- m :: m[key] == \<expr\>
    forall key :: key in m ==> m[key] == \<expr\>
