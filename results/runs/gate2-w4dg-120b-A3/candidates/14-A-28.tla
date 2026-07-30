---- MODULE MCBoulanger ----
EXTENDS Integers, Naturals

CONSTANTS N, MaxNat

BakerStates == {"idle", "trying", "critical"}

VARIABLES pc, ticket

vars == <<pc, ticket>>

TypeOK ==
    /\ pc \in [1..N -> BakerStates]
    /\ ticket \in [1..N -> 0..MaxNat]

Init ==
    /\ pc = [i \in 1..N |-> "idle"]
    /\ ticket = [i \in 1..N |-> 0]

Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "trying"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED <<>>

Enter(i) ==
    /\ pc[i] = "trying"
    /\ \A j \in 1..N : (pc[j] = "critical") => ticket[j] < ticket[i]
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<ticket>>

Exit(i) ==
    /\ pc[i] = "critical"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<ticket>>

Next == \E i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i \in 1..N : pc[i] = "critical" => \A j \in 1..N : (j # i) => pc[j] # "critical"

Inv ==
    /\ TypeOK
    /\ MutualExclusion

StateBound == \A i \in 1..N : ticket[i] < MaxNat

====