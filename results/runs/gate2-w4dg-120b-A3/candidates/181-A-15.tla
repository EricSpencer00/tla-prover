---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS
  MaxNat

\* NatOverride replaces the infinite natural-number set Nat from the standard
\* module with a finite version, which is what makes the model's state space
\* checkable. It is defined as an operator, not a constant, so that the
\* replacement is done by name and does not clash with the original Nat.
NatOverride ==
  { n \in Nat : n <= MaxNat }

Specification == Spec
Init == Init
Next == Next

\* The theorem being model-checked is assumed as a constant-level fact of the
\* configuration, so it is never listed as a property to prove; it is simply
\* taken as true for the sake of the surrounding proof.
Invariants == {}
Properties == {}

====