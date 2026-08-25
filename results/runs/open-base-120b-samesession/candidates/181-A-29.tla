---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers set used for model checking
NatOverride == 0 .. MaxNat

\* Simple evenness predicate
IsEven(m) == m % 2 = 0

\* Theorem to be assumed for the model checker
Theorem == \A n \in NatOverride : IsEven(2 * n)

ASSUME Theorem

\* Dummy state variable to give a concrete state space
VARIABLE dummy

INIT == dummy = 0

NEXT == dummy' = dummy

SPECIFICATION == INIT /\ [] [][NEXT]_<<dummy>>

INVARIANTS == Theorem

PROPERTIES == Theorem
====