---- MODULE W4Od14m8p3t1 ----
CONSTANTS Drones, Slots, NONE
VARIABLES assign, holds, coarse, fine

vars == <<assign, holds, coarse, fine>>

TypeOK ==
    /\ assign \in [Slots -> Drones \cup {NONE}]
    holds \in [Drones -> Slots \cup {NONE}]
    /\ coarse \in Drones \cup {NONE}
    /\ fine \in Drones \cup {NONE}

Init ==
    /\ assign = [s \in Slots |-> NONE]
    /\ holds = [d \in Drones |-> NONE]
    /\ coarse = NONE
    /\ fine = NONE

AcquireCoarse(d) ==
    /\ coarse = NONE
    /\ coarse' = d
    /\ UNCHANGED <<assign, holds, fine>>

AcquireFine(d) ==
    /\ coarse = d
    /\ fine = NONE
    /\ fine' = d
    /\ UNCHANGED <<assign, holds, coarse>>

Bind(d, s) ==
    /\ coarse = d
    /\ fine = d
    /\ holds[d] = NONE
    /\ assign[s] = NONE
    /\ assign' = [assign EXCEPT ![s] = d]
    /\ holds' = [holds EXCEPT ![d] = s]
    /\ UNCHANGED <<coarse, fine>>

ReleaseLocks(d) ==
    /\ coarse = d
    /\ coarse' = NONE
    /\ fine' = IF fine = d THEN NONE ELSE fine
    /\ UNCHANGED <<assign, holds>>

Unbind(d) ==
    /\ holds[d] # NONE
    /\ assign' = [assign EXCEPT ![holds[d]] = NONE]
    /\ holds' = [holds EXCEPT ![d] = NONE]
    /\ UNCHANGED <<coarse, fine>>

Next ==
    \/ \E d \in Drones : AcquireCoarse(d) \/ AcquireFine(d) \/ ReleaseLocks(d) \/ Unbind(d)
    \/ \E d \in Drones, s \in Slots : Bind(d, s)

Spec == Init /\ [][Next]_vars

AllocationCoherent == \A d \in Drones : holds[d] # NONE => assign[holds[d]] = d
====