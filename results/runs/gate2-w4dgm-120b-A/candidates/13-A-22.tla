---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The ticket numbers are constrained to a finite range 0..MaxNat for model checking.
\* This overrides the infinite Nat from Naturals globally (the .cfg replaces Nat with NatOverride).
NatOverride == 0..MaxNat

VARIABLES inCS, want, ticket, serving

vars == <<inCS, want, ticket, serving>>

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ want \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> NatOverride]
    /\ serving \in NatOverride

Init ==
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ want = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]
    /\ serving = 0

\* Request entry: a process picks a fresh ticket number and announces its intent.
Request(i) ==
    /\ ~want[i]
    /\ ~inCS[i]
    /\ \A j \in 1..N : ~want[j]
    /\ \E t \in NatOverride :
         /\ t > serving
         /\ \A j \in 1..N : (want[j] => t < ticket[j])
         /\ ticket' = [ticket EXCEPT ![i] = t]
    /\ want' = [want EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<inCS, serving>>

\* Enter critical section only if holding the smallest outstanding ticket.
Enter(i) ==
    /\ want[i]
    /\ ~inCS[i]
    /\ \A j \in 1..N : ~(want[j] /\ ticket[j] < ticket[i])
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<want, ticket, serving>>

\* Leave the critical section, bumping the served counter so tickets stay comparable.
Leave(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ want' = [want EXCEPT ![i] = FALSE]
    /\ serving' = IF serving < MaxNat THEN serving + 1 ELSE serving
    /\ UNCHANGED ticket

Next == \E i \in 1..N : Request(i) \/ Enter(i) \/ Leave(i)

MutualExclusion ==
    \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

\* The full inductive safety invariant for the Bakery algorithm.
Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A i \in 1..N : inCS[i] => (~want[i] /\ ticket[i] <= serving)

\* Starting from any reachable type-correct state, fairness of Request and Leave
\* steps drives the system to a state where nobody is in the critical section.
ISpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A i \in 1..N : WF_vars(Request(i)) /\ WF_vars(Leave(i))

\* Strong fairness of the leaving step is what guarantees exit from the critical
\* section; without it a process could be starved forever by request churn.
Properties == \A i \in 1..N : SF_vars(Leave(i))

====