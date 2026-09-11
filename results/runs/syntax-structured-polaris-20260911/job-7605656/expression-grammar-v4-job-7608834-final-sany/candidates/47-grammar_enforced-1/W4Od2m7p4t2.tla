---- MODULE W4Od2m7p4t2 ----
EXTENDS Naturals
CONSTANTS Dispatchers, Cap
VARIABLES active, readSnapshots
vars == <<active, readSnapshots>>

Init ==
  /\ active = 0
  /\ readSnapshots = [d \in Dispatchers |-> 0]

ActiveWithinCapacity == active <= Cap

Next ==
  /\ active' = active
  /\ UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : readSnapshots[d] < Cap
    /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] + 1 ELSE readSnapshots[d]]
    /\ UNCHANGED <<active>>
  \/ \E r \in Dispatchers, d \in Dispatchers : readSnapshots[r] < Cap
    /\ UNCHANGED <<active, readSnapshots>>

Spec == Init /\ [][Next]_vars

====