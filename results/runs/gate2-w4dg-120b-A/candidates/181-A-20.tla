---- MODULE MC_sums_even ----
EXTENDS Naturals

\* Model-checking configuration module for the proof that the double of any
\* natural number is even.  It inherits the mathematical definitions from the
\* base specification and overrides the natural number set with a finite range,
\* so TLC can check the theorem on a bounded domain.
CONSTANTS MaxNat, Nat

ZeroNat == 0

\* The invariant is the double-of-a-number-is-even theorem.  It is assumed to
\* hold as a constant-level assumption for model checking.
EvenDouble == \A n \in Nat : (2 * n) % 2 = 0

SpecBound == Nat = 0 .. MaxNat

Specification == SpecBound
Init == SpecBound
Next == SpecBound
Invariants == EvenDouble
Properties == SpecBound
====