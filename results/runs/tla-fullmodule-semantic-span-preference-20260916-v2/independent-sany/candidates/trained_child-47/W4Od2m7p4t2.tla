---- MODULE W4Od2m7p4t2 ----
EXTENDS Naturals
CONSTANTS Dispatchers, Cap
VARIABLES active, readSnapshots
vars == <<active, readSnapshots>>

Init == active = 0
\* Each dispatcher has read the initial active count
\* and has no stale snapshot
readSnapshots = [d \in Dispatchers |-> 0]

Next == \/ \E d \in Dispatchers : active < Cap \/\
      \/ \E d \in Dispatchers, r \in 0..Cap : readSnapshots[d] = r /\ active < Cap /\ readSnapshots' = readSnapshots \/ [d |-> r+1]
      \/ \E d \in Dispatchers : readSnapshots[d] > active /\ active < Cap /\ readSnapshots' = readSnapshots
      \/ \E d \in Dispatchers : active > 0 /\ readSnapshots' = [d |-> readSnapshots[d]-1]

Spec == Init /\ [][Next]_vars

ActiveWithinCapacity == active <= Cap
====