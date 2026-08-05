---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,
    MaxNat

VARIABLES
    entering,
    ticket,
    inCS

vars == <<entering, ticket, inCS>>

TypeOK ==
    /\ entering \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ inCS \subseteq (1..N)

Inv ==
    /\ entering \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ inCS \subseteq (1..N)
    /\ \A i \in inCS : entering[i] = TRUE

NatOverride == 0..MaxNat

MutualExclusion == \A i, j \in inCS : i = j

Init ==
    /\ entering = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]
    /\ inCS = {}

Request(i) ==
    /\ entering[i] = FALSE
    /\ entering' = [entering EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, inCS>>

Enter(i) ==
    /\ entering[i] = TRUE
    /\ \A j \in inCS :
        entering[j] = FALSE \/ ticket[j] > ticket[i] \/ (ticket[j] = ticket[i] /\ j > i)
    /\ inCS' = inCS \cup {i}
    /\ UNCHANGED <<entering, ticket>>

Exit(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ entering' = [entering EXCEPT ![i] = FALSE]
    /\ UNCHANGED ticket

Bump(i) ==
    /\ \A k \in 1..N : ticket[k] < MaxNat
    /\ ticket' = [i \in 1..N |-> IF entering[i] THEN (ticket[i] + 1) % (MaxNat + 1) ELSE ticket[i]]
    /\ UNCHANGED <<entering, inCS>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)
    \/ \E i \in 1..N : Bump(i)

ISpec == Init /\ [][Next]_vars

====