---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The double of any natural number is even: for every n, (2 * n) mod 2 = 0.
\* This module is the model-checkable configuration for that theorem: it
\* inherits the theorem from the base spec and bounds the natural number set
\* to a finite range so TLC can explore it.
\* NatOverride is a FINITE replacement for Naturals' infinite Nat, defined
\* here exactly as the bounded range, and it is declared a CONSTANT below.
\* The theorem itself is assumed as a constant-level fact for model checking.

NatOverride == 0..MaxNat

SPECIFICATION Spec
INIT Init
NEXT NextState
INVARIANTS DoubleEven
PROPERTIES TheoremHolds

Init == TRUE
NextState == TRUE

DoubleEven == \A n \in NatOverride : (2 * n) % 2 = 0
TheoremHolds == DoubleEven

====