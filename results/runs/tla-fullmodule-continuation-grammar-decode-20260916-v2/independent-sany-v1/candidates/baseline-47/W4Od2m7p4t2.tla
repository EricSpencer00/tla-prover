---- MODULE W4Od2m7p4t2 ----
EXTENDS Naturals
CONSTANTS Dispatchers, Cap
VARIABLES active, readSnapshots
vars == <<active, readSnapshots>>

Init ==
  /\ active = 0
  /\ readSnapshots = [d \in Dispatchers |-> 0]

ActiveWithinCapacity ==
  /\ active \in 0..Cap
  /\ readSnapshots \in [d \in Dispatchers |-> 0..active]

Next ==
  /\ \E d \in Dispatchers : readSnapshots[d] < active
    /\ \E d \in Dispatchers : readSnapshots' = readSnapshots \cup {[d |-> readSnapshots[d] + 1]}
    /\ UNCHANGED <<active>>
  \/ \E d \in Dispatchers : \E d' \in Dispatchers : readSnapshots[d] = readSnapshots[d']
    /\ \E d \in Dispatchers : readSnapshots[d] < Cap
    /\ \E d \in Dispatchers : readSnapshots' = readSnapshots \cup {[d |-> readSnapshots[d] + 1]}
    /\ UNCHANGED <<active>>
  \/ \E d \in Dispatchers : active' = active - 1
    /\ UNCHANGED <<readSnapshots>>

Spec == Init /\ [][Next]_vars

====