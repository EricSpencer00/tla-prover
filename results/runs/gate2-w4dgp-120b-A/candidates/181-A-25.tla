---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* The base theorem uses the infinite set `Nat`. For model checking we replace it with a
\* finite version of the same name. NatOverride is a new operator that implements the
\* replaced set; each entry in the .cfg maps the name on the left (the one used in the
\* base spec) to the operator defined here on the right.
NatOverride ==
  UNION { 0..k : k \in 0..MaxNat }

Nat == NatOverride

====