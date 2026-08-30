---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite override for the natural number set, used only in this
\* checking module; the base spec's natural numbers are still infinite.
NatOverride == 0..MaxNat

\* The theorem from the base spec is assumed here as a constant-level
\* truth so TLC can still explore the finite state space it defines.
TheoremEvenDoubling == \A x \in NatOverride : (2 * x) % 2 = 0

\* The base spec's main specification that this checking module feeds into.
SPECIFICATION == TheoremEvenDoubling

INIT == TRUE

NEXT == FALSE

INVARIANTS == TheoremEvenDoubling

PROPERTIES == TheoremEvenDoubling

====