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
  \/ \E d \in Dispatchers : /\ readSnapshots[d] < Cap
                      /\ readSnapshots' = readSnapshots
                      /\ UNCHANGED {<<active>>}
                      /\ \E d \in Dispatchers :
                          /\ readSnapshots[d] = active
                          /\ readSnapshots' = [d' \in Dispatchers |-> IF d' = d THEN active + 1 ELSE readSnapshots[d']]
                          /\ active' = active + 1
                      /\ \A d \in Dispatchers :
                          readSnapshots[d] # active
                      /\ UNCHANGED {active}
                      /\ \E d \E d' \in Dispatchers :
                          /\ d # d'
                          /\ readSnapshots[d] # readSnapshots[d']
                          /\ readSnapshots' = readsnapshots
                      /\ UNCHANGED vars
  \/ \E d \E d' : d # d'
                 /\ UNCHANGED vars
                 /\ UNCHANGED readSnapshots

Spec == Init /\ [][Next]_vars

====