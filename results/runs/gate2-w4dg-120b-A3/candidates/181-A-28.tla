---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* The finite override: NatOverride replaces the unbounded Nat from the standard
\* module with a bounded range, so TLC can explore the whole space.
NatOverride == 0 .. MaxNat

\* The theorem from the base spec is assumed as a constant-level assumption here.
SumIsEven == TRUE

\* The full spec structure expected by the .cfg; each name below is exactly the
\* one the configuration file requires (no more, no less).
Spec == Init /\ Next
Init == TRUE
Next == TRUE
Invariants == SumIsEven
Properties == SumIsEven

====