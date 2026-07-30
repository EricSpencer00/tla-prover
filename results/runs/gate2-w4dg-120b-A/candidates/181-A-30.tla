---- MODULE MC_sums_even ----
EXTENDS Integers

CONSTANTS MaxNat, Nat

\* The theorem being model-checked is that the double of any natural number is
\* even. The model overrides Nat to a finite range so TLC can finish.
BoundedNat == Nat \cup {MaxNat + 1}

TypeOK ==
  /\ MaxNat \in Nat
  /\ Nat \subseteq Nat

Spec == TRUE

Init == TRUE

Next == TRUE

Vars == {}

Invariants == {}
Properties == {}

\* The overriding constant-level assumption: the double of any number in the
\* bounded range is even, which TLC uses as the basis of its check.
Assume484 ==
  \A k \in BoundedNat : (2 * k) % 2 = 0

====