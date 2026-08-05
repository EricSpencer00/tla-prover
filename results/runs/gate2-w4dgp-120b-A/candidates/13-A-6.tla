---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES entering, ticket, cs

vars == <<entering, ticket, cs>>

TypeOK ==
    /\ entering \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ cs \in [1..N -> BOOLEAN]

MutualExclusion ==
    \A i \in 1..N:
        cs[i] => (\A j \in 1..N: j = i \/ ticket[i] <= ticket[j])

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A i \in 1..N: cs[i] => entering[i]
    /\ \A i, j \in 1..N:
        (cs[i] /\ entering[j] /\ i # j) => (ticket[i] <= ticket[j])

Init ==
    /\ entering = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]
    /\ cs = [i \in 1..N |-> FALSE]

Request(i) ==
    /\ ~entering[i]
    /\ ~cs[i]
    /\ entering' = [entering EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = MaxNat]
    /\ cs' = cs

Ticket(i) ==
    /\ entering[i]
    /\ \A j \in 1..N: ~cs[j]
    /\ \A j \in 1..N: ~entering[j] => ticket[i] <= ticket[j]
    /\ cs' = [cs EXCEPT ![i] = TRUE]
    /\ entering' = [entering EXCEPT ![i] = FALSE]
    /\ UNCHANGED ticket

Exit(i) ==
    /\ cs[i]
    /\ cs' = [cs EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<entering, ticket>>

Next ==
    \/ \E i \in 1..N: Request(i)
    \/ \E i \in 1..N: Ticket(i)
    \/ \E i \in 1..N: Exit(i)

ISpec == Init /\ [][Next]_vars

====