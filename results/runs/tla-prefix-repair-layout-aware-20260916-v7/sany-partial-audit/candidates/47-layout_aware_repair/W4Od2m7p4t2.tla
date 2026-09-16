---- MODULE W4Od2m7p4t2 ----
EXTENDS Naturals
CONSTANTS Dispatchers, Cap
VARIABLES active, readSnapshots

vars == <<active, readSnapshots>>

Init == /\ active = 0
       /\ readSnapshots = [d \in Dispatchers |-> 0]

Next == \/ active' = active
       \/ active' = active + 1
       \/ active' = active - 1
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots[d] = active /\ active < Cap
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots[d] = active /\ active < Cap
        /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] + 1 ELSE readSnapshots[d] :> Dispatchers \ {d} ]

Spec == Init /\ [][Next]_vars

ActiveWithinCapacity == active <= Cap

====