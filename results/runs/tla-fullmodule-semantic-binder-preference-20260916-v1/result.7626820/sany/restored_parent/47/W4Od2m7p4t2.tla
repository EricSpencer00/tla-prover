---- MODULE W4Od2m7p4t2 ----
EXTENDS Naturals
CONSTANTS Dispatchers, Cap
VARIABLES active, readSnapshots

vars == <<active, readSnapshots>>

Init == /\ active = 0
       /\ readSnapshots = [d \in Dispatchers |-> 0]

Next == \/ active' = active
       \/ active' = active + 1
       /\ readSnapshots' = [d \in Dispatchers |
                          IF readSnapshots[d] = active
                          THEN readSnapshots' = [d' \in Dispatchers |-> IF d' = d THEN active + 1 ELSE readSnapshots[d']]
                          ELSE readSnapshots']

Spec == Init /\ [][Next]_vars

ActiveWithinCapacity == active <= Cap

====