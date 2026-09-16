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
       \/ \E d0 \in Dispatchers : readSnapshots[d0] < Cap /\ readSnapshots[d0] = active
          /\ \A d1 \in Dispatchers : readSnapshots[d1] < Cap
          /\ \A d2 \in Dispatchers : readSnapshots[d2] = active
          /\ \A d3 \in Dispatchers : readSnapshots' = [e \in Dispatchers |-> IF e = d3 THEN readSnapshots[e] + 1 ELSE readSnapshots[e]]
          /\ active' = active + 1
       /\ \E d4 \in Dispatchers : readSnapshots[d4] < Cap /\ readSnapshots[d4] = active
          /\ \A d5 \in Dispatchers : readSnapshots[d5] < Cap
          /\ \A d6 \in Dispatchers : readSnapshots[d6] = active
          /\ \A d7 \in Dispatchers : readSnapshots' = [e \in Dispatchers |-> IF e = d7 THEN readSnapshots[e] ELSE readSnapshots[e]]
          /\ active' = active

Spec == Init /\ [][Next]_vars

ActiveWithinCapacity == active # Cap

====