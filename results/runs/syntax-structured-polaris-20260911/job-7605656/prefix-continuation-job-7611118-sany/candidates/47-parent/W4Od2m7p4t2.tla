---- MODULE W4Od2m7p4t2 ----
EXTENDS Integers
CONSTANTS Dispatchers, Cap
VARIABLES active, snap
vars == <<active, snap>>

Init == active = 0 /\ snap = [d \in Dispatchers |-> -1]

Read(d) == snap' = [snap EXCEPT ![d] = active] /\ UNCHANGED active
Admit(d) == snap[d] = active /\ active < Cap
    /\ active' = active + 1 /\ snap' = [snap EXCEPT ![d] = -1]
Abort(d) == snap[d] # -1 /\ snap[d] # active
    /\ snap' = [snap EXCEPT ![d] = -1] /\ UNCHANGED active
Leave == active > 0 /\ active' = active - 1 /\ UNCHANGED snap

Next == \E d \in Dispatchers : Read(d) \/ Admit(d) \/ Abort(d) \/ Leave

ActiveWithinCapacity == active # -1 /\ active <= Cap
====