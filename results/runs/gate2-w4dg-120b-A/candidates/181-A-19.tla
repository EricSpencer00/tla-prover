---- MODULE MC_sums_even ----
EXTENDS Integers, FiniteSets

\* This configuration module bounds the natural-number set to a finite range
\* so that TLC can model-check the theorem: for every n, 2*n is even.
\* The theorem itself is assumed here as a constant-level assumption.

CONSTANTS MaxNat, Nat

\* Model bounds the natural number set to 0..MaxNat, and Nat is the bounded set.
BoundedNat == 0 .. MaxNat

\* The invariant is the theorem itself, pulled into the model as a property.
EvenDouble(n) == (2 * n) % 2 = 0

\* There are no actions beyond the identity; the spec has a single stuttering step.
Spec == TRUE

Init == TRUE

Next == TRUE

TypeOK == TRUE

\* The invariant is the assumed theorem, applied to every bounded value.
BoundedEven == \A n \in BoundedNat : EvenDouble(n)

====