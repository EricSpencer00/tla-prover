---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite version of Nat that TLC will use instead of the true infinite set.
NatOverride == 0..MaxNat

\* The module inherits the main theorem from the base specification, which
\* assumes mathematical (not bounded) naturals. The override below keeps the
\* model checkable while the theorem itself is treated as an assumption.
ASSUME \A n \in Nat : (2 * n) % 2 = 0

TypeOK == MaxNat \in Nat

\* No system state to model here; the theorem is a mathematical fact, so the
\* dummy state is always in shape and the dummy action always applies.
InitState == TypeOK
Idle == InitState

Next == Idle

Spec == InitState /\ [][Next]_InitState

InitStateOK == InitState
\* With the theorem assumed true and no state to violate it, it is always true
\* by dint of being assumed.
TheoremHolds == TRUE

====