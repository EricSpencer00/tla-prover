---- MODULE W4Od2m7p4t2 ----
EXTENDS Naturals
CONSTANTS Dispatchers, Cap
VARIABLES active, readSnapshots
vars == <<active, readSnapshots>>

Init ==
  active = 0
  readSnapshots = [d \in Dispatchers |-> 0]

Next ==
  /\ \E d \in Dispatchers : readSnapshots[d] < Cap
    /\ readSnapshots' = [d \in Dispatchers |-> IF d = d'
      THEN readSnapshots[d] + 1
      ELSE readSnapshots[d]
    ]
    /\ UNCHANGED <<active, readSnapshots>> \* dispatcher failed to admit robot
  \/ \E d \in Dispatchers : readSnapshots[d] > 0
    /\ active < Cap
    /\ readSnapshots' = [d \in Dispatchers |-> IF d = d'
      THEN readSnapshots[d] - 1
      ELSE readSnapshots[d]
    ]
    /\ active' = active + 1
    /\ UNCHANGED <<readSnapshots>>

Spec == Init /\ [][Next]_vars

ActiveWithinCapacity == active <= Cap
====