---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, comp, tickets, served

vars == <<cs, comp, tickets, served>>

NatOverride == {0, 1, 2, 3}

TypeOK ==
    /\ cs \in 0..N
    /\ comp \in [1..N -> NatOverride]
    /\ tickets \in [1..N -> NatOverride]
    /\ served \subseteq 1..N

Init ==
    /\ cs = 0
    /\ comp = [i \in 1..N |-> 0]
    /\ tickets = [i \in 1..N |-> 0]
    /\ served = {}

Request(i) ==
    /\ cs = 0
    /\ comp[i] = 0
    /\ tickets[i] < MaxNat
    /\ tickets' = [tickets EXCEPT ![i] = tickets[i] + 1]
    /\ comp' = [comp EXCEPT ![i] = tickets[i] + 1]
    /\ UNCHANGED <<cs, served>>

Enter(i) ==
    /\ cs = 0
    /\ comp[i] # 0
    /\ cs' = i
    /\ comp' = [comp EXCEPT ![i] = 0]
    /\ UNCHANGED <<tickets, served>>

Exit(i) ==
    /\ cs = i
    /\ cs' = 0
    /\ served' = served \cup {i}
    /\ UNCHANGED <<comp, tickets>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i \in 1..N : (cs = i) => (\A j \in 1..N : j # i => comp[j] = 0)

Inv ==
    /\ tickets \in [1..N -> NatOverride]
    /\ served \subseteq 1..N

====