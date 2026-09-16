---- MODULE W4Od2m7p4t2 ----
EXTENDS Naturals
CONSTANTS Dispatchers, Cap
VARIABLES active, readSnapshots
vars == <<active, readSnapshots>>

Init == active = 0
\* Each dispatcher has read the initial active count
\* and has no stale snapshot
readSnapshots = [d \in Dispatchers |-> 0]

ActiveWithinCapacity == active <= Cap

Next == \E d \in Dispatchers : (
    readSnapshots[d] < active \/ 
    (readSnapshots[d] = active /\ active < Cap /\ active' = active + 1) \/ 
    (readSnapshots' = [d' \in Dispatchers |-> IF d' = d THEN readSnapshots[d] ELSE readSnapshots[d']]) 
)

Spec == Init /\ [][Next]_vars

====