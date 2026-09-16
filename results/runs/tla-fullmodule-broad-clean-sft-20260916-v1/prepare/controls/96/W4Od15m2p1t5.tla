---- MODULE W4Od15m2p1t5 ----
EXTENDS Integers

Members == {"m1", "m2"}
NONE == "none"
MaxVer == 4

VARIABLES ver, appliedVers, phase, votes, txnBase

vars == <<ver, appliedVers, phase, votes, txnBase>>

Init ==
    /\ ver = 0
    /\ appliedVers = {}
    /\ phase = "idle"
    /\ votes = [m \in Members |-> NONE]
    /\ txnBase = 0

Propose ==
    /\ phase = "idle"
    /\ ver < MaxVer
    /\ txnBase' = ver
    /\ phase' = "voting"
    /\ votes' = [m \in Members |-> NONE]
    /\ UNCHANGED <<ver, appliedVers>>

Vote(m, v) ==
    /\ phase = "voting"
    /\ votes[m] = NONE
    /\ votes' = [votes EXCEPT ![m] = v]
    /\ UNCHANGED <<ver, appliedVers, phase, txnBase>>

Commit ==
    /\ phase = "voting"
    /\ \A m \in Members : votes[m] = "yes"
    /\ txnBase = ver
    /\ ver' = ver + 1
    /\ appliedVers' = appliedVers \cup {txnBase}
    /\ phase' = "done"
    /\ UNCHANGED <<votes, txnBase>>

AdminCommit ==
    /\ phase = "voting"
    /\ txnBase = ver
    /\ ver' = ver + 1
    /\ appliedVers' = appliedVers \cup {txnBase}
    /\ phase' = "done"
    /\ UNCHANGED <<votes, txnBase>>

Abort ==
    /\ phase = "voting"
    /\ \E m \in Members : votes[m] = "no"
    /\ phase' = "done"
    /\ UNCHANGED <<ver, appliedVers, votes, txnBase>>

Reset ==
    /\ phase = "done"
    /\ phase' = "idle"
    /\ UNCHANGED <<ver, appliedVers, votes, txnBase>>

Quiesce ==
    /\ phase = "idle"
    /\ ver = MaxVer
    /\ UNCHANGED vars

Next ==
    \/ Propose
    \/ \E m \in Members, v \in {"yes", "no"} : Vote(m, v)
    \/ Commit
    \/ AdminCommit
    \/ Abort
    \/ Reset
    \/ Quiesce

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ ver \in 0..MaxVer
    /\ appliedVers \subseteq (0..MaxVer)
    /\ phase \in {"idle", "voting", "done"}
    /\ votes \in [Members -> {NONE, "yes", "no"}]
    /\ txnBase \in 0..MaxVer

NoLostAmendment ==
    appliedVers = (0..(ver - 1))

====