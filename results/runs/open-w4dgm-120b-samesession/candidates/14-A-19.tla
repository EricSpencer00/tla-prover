---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, ticket, inCS, door

TypeOK ==
    /\ cs \in 0..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ inCS \in 0..N
    /\ door \in [1..N -> {"unknown", "open", "closed"}]

Init ==
    /\ cs = 0
    /\ ticket = [i \in 1..N |-> 0]
    /\ inCS = 0
    /\ door = [i \in 1..N |-> "unknown"]

Request(i) ==
    /\ ticket[i] = 0
    /\ \E k \in 1..MaxNat : ticket' = [ticket EXCEPT ![i] = k]
    /\ UNCHANGED <<cs, inCS, door>>

Enter(i) ==
    /\ cs = 0
    /\ ticket[i] # 0
    /\ cs' = i
    /\ inCS' = inCS + 1
    /\ door' = [door EXCEPT ![i] = "open"]
    /\ UNCHANGED ticket

Exit(i) ==
    /\ cs = i
    /\ cs' = 0
    /\ inCS' = inCS - 1
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ door' = [door EXCEPT ![i] = "closed"]

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

Spec ==
    /\ Init
    /\ [][Next]_<<cs, ticket, inCS, door>>

MutualExclusion == inCS <= 1

Inv ==
    /\ inCS <= 1
    /\ \A i \in 1..N : cs = i => ticket[i] # 0
    /\ \A i \in 1..N : door[i] = "open" => cs = i

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====