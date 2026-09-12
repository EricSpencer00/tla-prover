---- MODULE W4Od2m7p4t2 ----
EXTENDS Integers, FiniteSets

CONSTANTS Dispatchers, Cap

VARIABLES active, readSnapshots

vars == <<active, readSnapshots>>

Init ==
  /\ active = 0
  /\ readSnapshots = [d \in Dispatchers |-> 0]

ActiveWithinCapacity ==
  /\ active \in 0..Cap
  /\ readSnapshots \in [d \in Dispatchers |-> 0..Cap]

Next ==
  \/ \E d \in Dispatchers : (readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/ \E r \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active)
    \/ \E r \in Dispatchers, d \in Dispatchers : (readSnapshots[r] < Cap /\ readSnapshots[r] = active /\ readSnapshots[d] < Cap /\ readSnapshots[d] = active)
    \/