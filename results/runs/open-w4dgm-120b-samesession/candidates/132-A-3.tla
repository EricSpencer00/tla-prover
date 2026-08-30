---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* Model-checking configuration for the Boyer-Moore majority vote algorithm.
\* This module chooses concrete values and a length bound, then re-instantiates
\* the generic majority vote spec (the rest of the actions/properties are all
\* inherited).  The seq-constructor is replaced with a bounded, finite version
\* so the model stays finite and checkable.

CONSTANTS A, B, C, bound

\* Concrete, finite value set derived from the configuration constants.
Values == {A, B, C}

\* BoundedSeq replaces the standard Seq from Sequences with a finite, bounded
\* version of it (bounded by the 'bound' model parameter).  It is kept EXTENDS
\* Sequences so the rest of the imported spec can still refer to it by name.
BoundedSeq(S) ==
  /\ \E n \in 0..bound : S = [k \in 1..n |-> S[k]]
  /\ \A i \in 1..bound : S[i] \in Values

\* The generic majority vote spec is instantiated here with concrete values and
\* the bounded sequence operator, providing Init, Next, Spec, TypeOK,
\* Correct, and Inv to this configuration module.
\* The override syntax applies only to definitions introduced in this module.
\* Nothing else is redeclared here; all other operators come from the spec.
\* (The override block is deliberately empty except for BoundedSeq.)
Extends == {Sequences}
\* The following LOCAL block is just to hold the override syntax; it does
\* not actually introduce any new definitions beyond BoundedSeq above.
LOCAL
  BEGIN
    BoundedSeq == BoundedSeq
    \* The generic spec's Seq name is shadowed by the override.
  END

\* Re-expose the instantiated spec's operators under the required names.
Init == Init
Next == Next
Spec == Spec

TypeOK == TypeOK
Correct == Correct
Inv == Inv

====