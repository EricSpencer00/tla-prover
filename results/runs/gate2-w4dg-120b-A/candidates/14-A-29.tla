---- MODULE MCBoulanger ----
EXTENDS Naturals

\* A finite-range version of the Boulanger mutual exclusion algorithm, for
\* model checking.  The full set of natural numbers is shadowed by a finite
\* range 0..MaxNat, and a state constraint keeps ticket numbers below the
\* upper bound.
CONSTANTS N, MaxNat, Nat

Bump(x) == IF x < MaxNat THEN x + 1 ELSE x

VARIABLES cs, want, inCS, ticket
vars == <<cs, want, inCS, ticket>>

TypeOK ==
    /\ cs \in {0, 1}
    /\ want \in [1..N -> BOOLEAN]
    /\ inCS \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]

Init ==
    /\ cs = 0
    /\ want = [i \in 1..N |-> FALSE]
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]

Ask(i) ==
    /\ ~want[i]
    /\ cs = 0
    /\ want' = [want EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED <<cs, inCS>>

Preempt(i) ==
    /\ cs = 1
    /\ cs' = 0
    /\ UNCHANGED <<want, inCS, ticket>>

Enter(i) ==
    /\ cs = 0
    /\ want[i]
    /\ \A j \in 1..N : ~want[j] \/ ticket[j] > ticket[i]
    /\ cs' = 1
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<want, ticket>>

Exit(i) ==
    /\ cs = 1
    /\ inCS[i]
    /\ cs' = 0
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ want' = [want EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = Bump(ticket[i])]

Next ==
    \/ \E i \in 1..N : Ask(i)
    \/ \E i \in 1..N : Preempt(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

\* Every ticket is strictly below the finite bound, so the finite Nat range
\* never needs to be expanded during model checking.
BoundedTickets == \A i \in 1..N : ticket[i] < MaxNat

\* The behavioral spec (full Next) is used for checking, so the full invariant
\* needs the stronger type discipline rather than the weakened one on the
\* inductive spec.
Inv == TypeOK /\ BoundedTickets

====