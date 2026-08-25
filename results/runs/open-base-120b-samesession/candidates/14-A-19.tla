---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite override for the natural numbers used by the model checker.
\* The .cfg file will replace occurrences of Nat with NatOverride.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint: ticket (number) values must stay strictly below MaxNat.
\* The bakery algorithm uses the variable `number` to hold each process's
\* ticket.  This constraint prunes states that would require values
\* outside the finite range.
\* ----------------------------------------------------------------------
StateConstraint == 
    \A i \in 1 .. N : number[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification of the system for model checking.
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_vars /\ StateConstraint

====