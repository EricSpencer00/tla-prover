---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS
    N, MaxNat

VARIABLES
    inCS, request, serving, maxServed

vars == <<inCS, request, serving, maxServed>>

NatOverride == 0..MaxNat

TypeOK ==
    /\ inCS \in [1..N -> 0..(MaxNat + 1)]
    /\ request \in [1..N -> NatOverride]
    /\ serving \in [1..N -> NatOverride]
    /\ maxServed \in NatOverride

Init ==
    /\ inCS = [i \in 1..N |-> 0]
    /\ request = [i \in 1..N |-> 0]
    /\ serving = [i \in 1..N |-> 0]
    /\ maxServed = 0

Request(i) ==
    /\ request[i] = 0
    /\ request' = [request EXCEPT ![i] = maxServed + 1]
    /\ UNCHANGED <<inCS, serving, maxServed>>

Enter(i) ==
    /\ request[i] # 0
    /\ serving[i] = 0
    /\ inCS' = [inCS EXCEPT ![i] = request[i]]
    /\ serving' = [serving EXCEPT ![i] = request[i]]
    /\ UNCHANGED <<request, maxServed>>

Exit(i) ==
    /\ inCS[i] # 0
    /\ inCS' = [inCS EXCEPT ![i] = 0]
    /\ serving' = [serving EXCEPT ![i] = 0]
    /\ maxServed' = IF maxServed < request[i] THEN request[i] ELSE maxServed
    /\ request' = [request EXCEPT ![i] = 0]

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in 1..N : (inCS[i] # 0 /\ inCS[j] # 0) => inCS[i] = inCS[j]

Inv ==
    /\ \A i, j \in 1..N :
        (serving[i] # 0 /\ serving[j] # 0 /\ i # j) => serving[i] = serving[j]
    /\ \A i \in 1..N : request[i] # 0 => serving[i] = request[i]
    /\ \A i \in 1..N : inCS[i] # 0 => inCS[i] = serving[i]
    /\ \A i \in 1..N : serving[i] <= maxServed

StateConstraint == \A i \in 1..N : serving[i] < MaxNat

====