---- MODULE W4Od2m7p4t2 ----
CONSTANTS Dispatchers, Cap

VARIABLES active, readSnap, dispatcher

vars == <<active, readSnap, dispatcher>>

Init == active = 0 /\ readSnap = [d \in Dispatchers :-> 0] /\ dispatcher \in Dispatchers

ActiveWithinCapacity == active <= Cap /\ readSnap \in [d \in Dispatchers :->[0, Cap]]

Next == \E d \in dispatcher : (
    readSnap[d] < active \/ 
    ((readSnap[d] = active /\ active <Cap /\ active' = active +  1) /\ dispatcher' = d) \/ 
    (readSnap' = [d' \in dispatcher :-> IF d' = d THEN  readSnap[d] ELSE readSnap[d']]) 
)

Spec ==Init /\ [][Next]_vars
====