---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Finite-range override for TLC: we bind Nat to a finite set 0..MaxNat rather than
\* the usual infinite natural numbers.
NatOverride == 0..MaxNat

\* The theorem from the base spec is assumed here as a constant-level fact for TLC.
SumDoubleIsEven == \A n \in NatOverride : (2 * n) % 2 = 0

Spec == SumDoubleIsEven

Init == SumDoubleIsEven

Next == SumDoubleIsEven

TypeOK == TRUE

\* No safety property beyond the theorem itself is modeled here.
Safety == TRUE

\* No liveness property is modeled here.
Liveness == TRUE

====