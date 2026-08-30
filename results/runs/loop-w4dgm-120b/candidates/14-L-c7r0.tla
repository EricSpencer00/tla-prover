---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES phase, ticket, served, idle

vars == <<phase, ticket, served, idle>>

TypeOK ==
    /\ phase \in [1..N -> {"idle", "trying", "critical"}]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ served \in 0..MaxNat
    /\ idle \subseteq 1..N

Init ==
    /\ phase = [i \in 1..N |-> "idle"]
    /\ ticket = [i \in 1..N |-> 0]
    /\ served = 0
    /\ idle = 1..N

Request(i) ==
    /\ phase[i] = "idle"
    /\ phase' = [phase EXCEPT ![i] = "trying"]
    /\ ticket' = [ticket EXCEPT ![i] = IF served < MaxNat THEN served + 1 ELSE served]
    /\ idle' = idle \ {i}
    /\ UNCHANGED served

Enter(i) ==
    /\ phase[i] = "trying"
    /\ \A j \in 1..N : phase[j] # "critical"
    /\ phase' = [phase EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<ticket, served, idle>>

Exit(i) ==
    /\ phase[i] = "critical"
    /\ phase' = [phase EXCEPT ![i] = "idle"]
    /\ served' = IF served < MaxNat THEN served + 1 ELSE served
    /\ idle' = idle \cup {i}
    /\ UNCHANGED ticket

Leave(i) ==
    /\ phase[i] = "trying"
    /\ phase' = [phase EXCEPT ![i] = "idle"]
    /\ idle' = idle \cup {i}
    /\ UNCHANGED <<ticket, served>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)
    \/ \E i \in 1..N : Leave(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i \in 1..N : phase[i] = "critical" => (\A j \in 1..N : (j # i) => phase[j] # "critical")

Inv ==
    /\ MutualExclusion
    /\ TypeOK

NatOverride == Nat

====