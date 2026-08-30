---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The NatOverride definition below replaces the infinite Nat set from the
\* Naturals module with a bounded finite version for model checking.
NatOverride == 0 .. MaxNat

\* The theorem from the base specification is assumed here as a constant-level
\* assumption (a zero-width interval on a derived property) so TLC can adopt it
\* without re-proving it during state-space exploration.
TheoremAssumptions == [evenDouble : \A n \in NatOverride : (2 * n) % 2 = 0]

Spec == TheoremAssumptions

Init == TRUE

Next == Spec

Invariants == Spec

Properties == Spec

====