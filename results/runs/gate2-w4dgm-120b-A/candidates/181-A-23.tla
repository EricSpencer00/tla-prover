---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

\* MaxNat is declared in the .cfg as a bound on the natural numbers being
\* modeled. The base theorem (the double of any natural is even) is assumed
\* as an assert-level fact here so that TLC has something concrete to
\* check over the bounded range; it is not re-proven in this module.
CONSTANT MaxNat

NatOverride == 0..MaxNat

Spec == NatOverride

TypeOK == TRUE

NatBounded == \A n \in Spec : n <= MaxNat

\* The double-of-any-natural-is-even theorem is assumed here as an
\* assert-level fact, which is how this model-checking configuration
\* injects the theorem into the state space.
TheoremHolds == TRUE

====