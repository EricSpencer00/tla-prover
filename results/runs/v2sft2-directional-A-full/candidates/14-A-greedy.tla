---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
\* The finite set of natural numbers used in this model
Nat == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State variables (inherited from the Boulanger specification)
\* ----------------------------------------------------------------------
VARIABLES ticket, next, inCS

\* ----------------------------------------------------------------------
\* Initial state (same as Boulanger, but with Nat restricted)
\* ----------------------------------------------------------------------
Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ next = 0
    /\ inCS = {}

\* ----------------------------------------------------------------------
\* Actions (same as Boulanger, but with Nat restricted)
\* ----------------------------------------------------------------------
\* Request a ticket
Request(i) ==
    /\ i \in 1..N
    /\ next \in Nat
    /\ ticket' = [ticket EXCEPT ![i] = next]
    /\ next' = (next + 1) % (MaxNat + 1)
    /\ UNCHANGED inCS

\* Enter critical section
Enter(i) ==
    /\ i \in 1..N
    /\ ticket[i] \in Nat
    /\ \A j \in 1..N : (j # i) => ticket[j] > ticket[i]
    /\ inCS' = inCS \cup {i}
    /\ UNCHANGED <<ticket, next>>

\* Exit critical section
Exit(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ UNCHANGED <<ticket, next>>

\* Next-state relation
Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in inCS : Exit(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<ticket, next, inCS>>

\* ----------------------------------------------------------------------
\* Safety invariants (inherited from Boulanger)
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in inCS : i = j

TypeOK ==
    /\ ticket \in [1..N -> Nat]
    /\ next \in Nat
    /\ inCS \subseteq 1..N

Inv ==
    \A i \in 1..N :
        (i \in inCS => ticket[i] = next)
        /\ (i \notin inCS => ticket[i] < next)

\* ----------------------------------------------------------------------
\* State constraint to keep ticket numbers strictly below MaxNat
\* ----------------------------------------------------------------------
StateConstraint ==
    \A i \in 1..N : ticket[i] < MaxNat

====