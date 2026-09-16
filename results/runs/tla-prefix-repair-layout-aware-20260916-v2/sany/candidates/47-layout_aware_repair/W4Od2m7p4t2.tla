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
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] + 1 ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] + 1 ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots' = [d \in Dispatchers |-> IF d = d' THEN readSnapshots[d] ELSE readSnapshots[d]]
       \/ \E d \in Dispatchers : readSnapshots[d] < Cap