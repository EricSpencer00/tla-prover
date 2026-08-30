---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat with a finite bounded range so
\* TLC can model check the theorem; it is defined here, not declared.
NatOverride == 0..MaxNat

\* SAFETY PROPERTY: the double of any natural number in the bounded range is even.
Theorem == \A x \in NatOverride : 2 * x \in NatOverride /\ (2 * x) % 2 = 0

Spec == TRUE
Init == TRUE
Next == TRUE
Invariants == {Theorem}
Properties == {Theorem}
====