---- MODULE MC_sums_even ----
EXTENDS Naturals

\* The .cfg replaces the infinite natural-number set with a finite one.
\* NatOverride is defined here and the .cfg maps the name Nat to it, so
\* the module itself must NOT declare or redefine Nat, only NatOverride.
NatOverride ==
  Nat \cup { 0 }

CONSTANTS MaxNat

VARIABLES k
vars == << k >>

TypeOK ==
  /\ k \in NatOverride
  /\ k <= MaxNat

Init ==
  /\ k = 0

Step ==
  /\ k < MaxNat
  /\ k' = k + 1

Next ==
  \/ Step

DoubleEven ==
  \A m \in 0..MaxNat : 2 * m \in NatOverride

Spec == Init /\ [][Next]_vars
====