---- MODULE W4Od1m0p0t5 ----
EXTENDS Integers
Planes = {"p1","p2"}
MaxV == 4
VARIABLES cleared, version, admin
Init == cleared = [p \in Planes |-> FALSE] /\ version = 0 /\ admin = FALSE
Clear(p) == (\A q \in Planes : ~cleared[q]) /\ version < MaxV /\ cleared' = [cleared EXCEPT ![p] = TRUE] /\ version' = version + 1 /\ admin' = admin
Vacate(p) == cleared[p] /\ version < MaxV /\ cleared' = [cleared EXCEPT ![p] = FALSE] /\ version' = version + 1 /\ admin' = admin
AdminClear == admin' = TRUE /\ cleared' = [p \in Planes |-> FALSE] /\ version' = version
Next == AdminClear \/ (\E p \in Planes : Clear(p) \/ Vacate(p))
vars == <<cleared, version, admin>>
Spec == Init /\ [][Next]_vars
OneRunwayUser == \A p1 \in Planes, p2 \in Planes : (cleared[p1] /\ cleared[p2]) => (p1 = p2)
====