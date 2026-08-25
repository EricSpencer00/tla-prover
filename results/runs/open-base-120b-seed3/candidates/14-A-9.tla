---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* Finite override of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers must stay strictly below MaxNat
StateConstraint == \A i \in 1..N: ticket[i] < MaxNat

\* Specification incorporating the original Boulanger init/next and the constraint
Spec == Init /\ [][Next]_vars /\ StateConstraint

====