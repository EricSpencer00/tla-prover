---- MODULE MajorityProof ----
EXTENDS MajoritySpec

CONSTANTS Value

TypeOK ==
    /\ seq \in [1..3 -> Value \cup {"none"}]
    /\ scanned \in 0..3
    /\ candidate \in Value \cup {"none"}
    /\ scanned = 3 => candidate \in Value

Init ==
    /\ seq = [i \in 1..3 |-> "none"]
    /\ scanned = 0
    /\ candidate = "none"

Input(v) ==
    /\ scanned < 3
    /\ scanned' = scanned + 1
    /\ seq' = [seq EXCEPT ![scanned + 1] = v]
    /\ UNCHANGED candidate

Vote(v) ==
    /\ scanned > 0
    /\ \/ candidate = "none"
       \/ candidate = v
    /\ candidate' = v
    /\ UNCHANGED <<seq, scanned>>

Discard ==
    /\ scanned > 0
    /\ scanned' = scanned - 1
    /\ seq' = [seq EXCEPT ![scanned] = "none"]
    /\ UNCHANGED candidate

Next ==
    \/ \E v \in Value : Input(v)
    \/ \E v \in Value : Vote(v)
    \/ Discard

Spec == Init /\ [][Next]_<<seq, scanned, candidate>>

Inv ==
    TypeOK /\ Correct
====