---- MODULE W4Od10m0p2t1 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Blocks, Total, MaxVer, MaxRetry

VARIABLES occ, ver, reqs, retries

vars == <<occ, ver, reqs, retries>>

NBlocks == Cardinality(Blocks)

Nxt(b) == (b + 1) % NBlocks

Msgs == [frm : Blocks, obs : 0..MaxVer]

TypeOK ==
    /\ occ \in [Blocks -> 0..Total]
    /\ ver \in [Blocks -> 0..MaxVer]
    /\ reqs \subseteq Msgs
    /\ retries \in 0..MaxRetry

Init ==
    /\ occ = [b \in Blocks |-> IF b = 0 THEN Total ELSE 0]
    /\ ver = [b \in Blocks |-> 0]
    /\ reqs = {}
    /\ retries = 0

Propose(b) ==
    /\ occ[b] > 0
    /\ reqs' = reqs \cup {[frm |-> b, obs |-> ver[b]]}
    /\ UNCHANGED <<occ, ver, retries>>

Commit(m) ==
    /\ m \in reqs
    /\ occ[m.frm] > 0
    /\ m.obs = ver[m.frm]
    /\ occ' = [occ EXCEPT ![m.frm] = @ - 1, ![Nxt(m.frm)] = @ + 1]
    /\ ver' = [ver EXCEPT ![m.frm] = (@ + 1) % (MaxVer + 1)]
    /\ reqs' = reqs \ {m}
    /\ UNCHANGED retries

Reject(m) ==
    /\ m \in reqs
    /\ m.obs # ver[m.frm]
    /\ reqs' = reqs \ {m}
    /\ retries' = IF retries < MaxRetry THEN retries + 1 ELSE retries
    /\ UNCHANGED <<occ, ver>>

ClearRetries ==
    /\ retries > 0
    /\ retries' = 0
    /\ UNCHANGED <<occ, ver, reqs>>

Next ==
    \/ \E b \in Blocks : Propose(b)
    \/ \E m \in reqs : Commit(m)
    \/ \E m \in reqs : Reject(m)
    \/ ClearRetries

Spec == Init /\ [][Next]_vars

TrainCount == occ[0] + occ[1] + occ[2]

ConservationOfTrains == TrainCount = Total
====