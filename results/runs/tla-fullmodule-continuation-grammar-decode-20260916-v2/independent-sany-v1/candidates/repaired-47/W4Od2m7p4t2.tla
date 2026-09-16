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
  \/ \E d \in Dispatchers : \E d1 \in Dispatchers : d1 # d /\ readSnapshots[d1] < active
    \/ \E d \in Dispatchers : readSnapshots[d] < active /\ readSnapshots[d] # readSnapshots[d]
    \/ \E d \in Dispatchers : readSnapshots' = readSnapshots \cup {[d |-> readSnapshots[d] + 1]}
    \/ \E d \in Dispatchers, d1 \in Dispatchers : readSnapshots[d1] < active /\ readSnapshots[d1] # readSnapshots[d]
      /\ UNCHANGED <<active>>
      /\ UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : readSnapshots[d] = active
    \/ \E d \in Dispatchers : readSnapshots[d] < Cap /\ readSnapshots[d] # readSnapshots[d]
      /\ UNCHANGED <<active>>
      /\ UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UNCHANGED <<active>>
    \/ \E d \in Dispatchers : UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UNCHANGED <<active>>
    \/ \E d \in Dispatchers : UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UNCHANGED <<active>>
    \/ \E d \in Dispatchers : UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UNCHANGED <<active>>
    \/ \E d \in Dispatchers : UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UNCHANGED <<active>>
    \/ \E d \in Dispatchers : UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UNCHANGED <<active>>
    \/ \E d \in Dispatchers : UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UNCHANGED <<active>>
    \/ \E d \in Dispatchers : UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UNCHANGED <<active>>
    \/ \E d \in Dispatchers : UNCHANGED readSnapshots
  \/ \E d \in Dispatchers : active < Cap /\ UN