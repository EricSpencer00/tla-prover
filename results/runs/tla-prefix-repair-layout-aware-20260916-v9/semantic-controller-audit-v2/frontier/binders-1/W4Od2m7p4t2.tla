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
          /\ \A d \in Dispatchers : readSnapshots[d] < Cap
          /\ \A d \in Dispatchers : readSnapshots[d] = active
          /\ \A d \in Dispatchers : readSnapshots' = [e \in Dispatchers |-> IF e = d THEN readSnapshots[e] + 1 ELSE readSnapshots[e]]
          /\ active' = active + 1
       /\ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots[d] = active
          /\ \A d \in Dispatchers : readSnapshots[d] < Cap
          /\ \A d \in Dispatchers : readSnapshots[d] = active
          /\ \A d \in Dispatchers : readSnapshots' = [e \in Dispatchers |-> IF e = d THEN readSnapshots[e] ELSE readSnapshots[e]]
          /\ active' = active

Spec == Init /\ [][Next]_vars

ActiveWithinCapacity == active # Cap

====