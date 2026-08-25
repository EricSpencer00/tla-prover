---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* Finite override for natural numbers used by TLC configuration
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers must stay strictly below the maximum
StateConstraint == 
    \A i \in 1..N : ticket[i] < MaxNat

====