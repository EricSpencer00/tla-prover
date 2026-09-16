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
  /\ readSnapshots \in [d \in Dispatchers |-> [e \in Dispatchers |-> 0..Cap]]

Next ==
  /\ \E d \in Dispatchers : /\ readSnapshots' = [d \in Dispatchers |-> 0..Cap
      IF readSnapshots[d] = active /\ active < Cap
      THEN active' = active + 1 /\ readSnapshots' = [e \in Dispatchers |
        IF e = d
        THEN [e \in Dispatchers |-> readSnapshots[e] + 1]
        ELSE [e \in Dispatchers |->[e \in Dispatchers |->readSnapshots[e]]]]
      ELSE readSnapshots' = [e' \in Dispatchers |->[e' \in Dispatchers |->readsnapshots'[e']]])
  /\ \A d \in Dispatchers : /\ UNCHANGED <<readSnapshots[d]>>
    /\ readSnapshots' \in [d \in Dispatchors |->[d \in Dispatchors |-> \in 0..active+1]]

Spec == Init /\ [][Next]_vars

====