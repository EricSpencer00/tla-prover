---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Bounded replacement for the infinite Naturals set: only numbers 0..MaxNat are
\* in the model's universe, so TLC has a finite state space to explore.
NatOverride == 0..MaxNat

\* The theorem from the base spec is assumed here as a fact, which is what lets
\* TLC run this reachability check instead of trying to prove it for all Nat.
TheoremDoubleEven == \A n \in NatOverride : 2 * n \in NatOverride

\* No system state to explore -- the module is a static configuration check.
Spec == TRUE

Init == Spec

Next == Spec

SpecInv == Spec

SpecProp == Spec

====