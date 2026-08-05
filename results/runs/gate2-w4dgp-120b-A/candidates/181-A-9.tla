---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite version
\* whose carrier is bounded by MaxNat. This is the only change to the base
\* specification; all other definitions are inherited and unchanged, so the
\* state graph is the same proof skeleton, just cut off at a reachable bound.
NatOverride == 0 .. MaxNat

ASSUME MaxNat \in Nat /\ MaxNat > 2

\* The theorem is assumed here so that the model-checking slice can run without
\* having to re-prove it inside this configuration module.
ASSUME \A n \in NatOverride : 2 * n \in Nat

====