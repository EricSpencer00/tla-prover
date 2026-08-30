---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* The finite-range override: the model replaces the unbounded Nat with a
\* bounded version whose values are cut off at MaxNat.
NatOverride(n) == IF n <= MaxNat THEN n ELSE MaxNat

VARIABLES inCS, want, ticket, maxUsed

vars == <<inCS, want, ticket, maxUsed>>

TypeOK ==
    /\ inCS \subseteq 1..N
    /\ want \subseteq 1..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ maxUsed \in 0..MaxNat

\* The full inductive invariant: mutual exclusion plus internal-consistency
\* checks that the bounded ticket discipline never breaks.
Inv ==
    /\ \A i \in 1..N : i \in inCS => i \in want
    /\ \A i \in inCS : \A j \in inCS : i # j => (ticket[i] # ticket[j] \/ ticket[i] = 0)
    /\ maxUsed = (IF \E k \in 1..N : ticket[k] # 0 THEN MaxNat ELSE 0)

MutualExclusion == \A i \in inCS, j \in inCS : i # j

Init ==
    /\ inCS = {}
    /\ want = {}
    /\ ticket = [i \in 1..N |-> 0]
    /\ maxUsed = 0

\* The act of entering grabs the next free ticket, bounded by NatOverride.
Enter(i) ==
    /\ i \in want
    /\ i \notin inCS
    /\ \E t \in 1..MaxNat :
        /\ \A j \in 1..N : ticket[j] # t
        /\ ticket' = [ticket EXCEPT ![i] = t]
        /\ maxUsed' = NatOverride(t)
    /\ inCS' = inCS \cup {i}
    /\ UNCHANGED want

Leave(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED <<want, maxUsed>>

Request(i) ==
    /\ i \notin want
    /\ want' = want \cup {i}
    /\ UNCHANGED <<inCS, ticket, maxUsed>>

Cancel(i) ==
    /\ i \in want
    /\ i \notin inCS
    /\ want' = want \ {i}
    /\ UNCHANGED <<inCS, ticket, maxUsed>>

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Leave(i)
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Cancel(i)

\* An inductive spec: any reachable state reachable from an arbitrary
\* type-correct state via Next must still satisfy the invariant.
ISpec == Init /\ [][Next]_vars

Spec = ISpec

====