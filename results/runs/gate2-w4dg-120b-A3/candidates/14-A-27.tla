---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES pc, ticket, owner, served

vars == <<pc, ticket, owner, served>>

StateConstraint == \A p \in 1..N : ticket[p] < MaxNat

Init ==
    /\ pc = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ owner = 0
    /\ served = 0

Begin(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] < MaxNat - 1 THEN ticket[p] + 1 ELSE ticket[p]]
    /\ UNCHANGED <<owner, served>>

Enter(p) ==
    /\ pc[p] = "waiting"
    /\ owner = 0
    /\ owner' = p
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, served>>

Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ owner' = 0
    /\ served' = (served + 1) % 4
    /\ UNCHANGED <<ticket>>

Next ==
    \/ \E p \in 1..N : Begin(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 1..N : pc[p] = "critical" => owner = p

TypeOK ==
    /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
    /\ ticket \in [1..N -> 0..(MaxNat - 1)]
    /\ owner \in 0..N
    /\ served \in 0..3

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ StateConstraint

====