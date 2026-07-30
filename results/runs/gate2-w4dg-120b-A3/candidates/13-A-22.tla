---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* An operator that replaces the infinite natural-number set with a bounded
\* version.  It is NOT declared itself; it is the definition for the name that
\* the .cfg replaces.
NatOverride ==
    Nat

VARIABLES inCS, number, choosing

vars == <<inCS, number, choosing>>

Init ==
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ number = [i \in 1..N |-> 0]
    /\ choosing = [i \in 1..N |-> FALSE]

Backoff(i) ==
    /\ ~inCS[i]
    /\ ~choosing[i]
    /\ number[i] = 0
    /\ number' = [number EXCEPT ![i] = 1]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED inCS

Acquire(i) ==
    /\ choosing[i]
    /\ \A k \in 1..N : ~inCS[k]
    /\ \A k \in 1..N : k # i => number[k] = 0 \/ number[i] < number[k]
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ number' = [number EXCEPT ![i] = 0]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]

Release(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ number' = [number EXCEPT ![i] = 0]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]

Next ==
    \/ \E i \in 1..N : Backoff(i)
    \/ \E i \in 1..N : Acquire(i)
    \/ \E i \in 1..N : Release(i)

\* The inductive specification: start from any type-correct state satisfying
\* the invariant, not just from Init.
ISpec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i \in 1..N, j \in 1..N : (i # j /\ inCS[i]) => ~inCS[j]

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ number \in [1..N -> 0..MaxNat]
    /\ choosing \in [1..N -> BOOLEAN]

Inv ==
    /\ MutualExclusion
    /\ \A i \in 1..N : inCS[i] => number[i] = 0
    /\ \A i \in 1..N : number[i] > 0 => ~inCS[i]

Spec == ISpec

====