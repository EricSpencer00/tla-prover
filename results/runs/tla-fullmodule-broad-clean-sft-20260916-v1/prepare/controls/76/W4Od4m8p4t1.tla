---------------------------- MODULE W4Od4m8p4t1 ----------------------------
EXTENDS Naturals

Dispatchers == {"d1", "d2"}
Msgs        == {"a1", "a2"}
Cap         == 2
NONE        == "none"

VARIABLES occupancy, coarse, fine, inflight
vars == <<occupancy, coarse, fine, inflight>>

TypeOK ==
    /\ occupancy \in 0..Cap
    /\ coarse \in Dispatchers \cup {NONE}
    /\ fine \in Dispatchers \cup {NONE}
    /\ inflight \subseteq Msgs

Init ==
    /\ occupancy = 0
    /\ coarse = NONE
    /\ fine = NONE
    /\ inflight = {}

SubmitMsg(m) ==
    /\ m \notin inflight
    /\ inflight' = inflight \cup {m}
    /\ UNCHANGED <<occupancy, coarse, fine>>

AcquireCoarse(d) ==
    /\ coarse = NONE
    /\ coarse' = d
    /\ UNCHANGED <<occupancy, fine, inflight>>

AcquireFine(d) ==
    /\ coarse = d
    /\ fine = NONE
    /\ fine' = d
    /\ UNCHANGED <<occupancy, coarse, inflight>>

Admit(d, m) ==
    /\ coarse = d
    /\ fine = d
    /\ m \in inflight
    /\ occupancy < Cap
    /\ occupancy' = occupancy + 1
    /\ inflight' = inflight \ {m}
    /\ coarse' = NONE
    /\ fine' = NONE

Depart ==
    /\ occupancy > 0
    /\ occupancy' = occupancy - 1
    /\ UNCHANGED <<coarse, fine, inflight>>

Next ==
    \/ \E m \in Msgs : SubmitMsg(m)
    \/ \E d \in Dispatchers : AcquireCoarse(d)
    \/ \E d \in Dispatchers : AcquireFine(d)
    \/ \E d \in Dispatchers, m \in Msgs : Admit(d, m)
    \/ Depart

BayWithinCapacity == occupancy <= Cap

Spec == Init /\ [][Next]_vars
=============================================================================