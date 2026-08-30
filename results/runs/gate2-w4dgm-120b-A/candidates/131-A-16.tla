---- MODULE MajorityProof ----
EXTENDS Integers

CONSTANTS Value

VARIABLES seq, candidate, scanned, countCand, concluded

vars == <<seq, candidate, scanned, countCand, concluded>>

TypeSet == [Value -> {"none","value1","value2"}]

TypeOK ==
    /\ seq \in [1..3 -> Value \cup {"none"}]
    /\ candidate \in Value \cup {"none"}
    /\ scanned \in 0..3
    /\ countCand \in 0..3
    /\ concluded \in BOOLEAN

Init ==
    /\ seq = [i \in 1..3 |-> "none"]
    /\ candidate = "none"
    /\ scanned = 0
    /\ countCand = 0
    /\ concluded = FALSE

Head == IF scanned = 0 THEN "none" ELSE seq[scanned]

ScanValue(v) ==
    /\ concluded = FALSE
    /\ seq[scanned + 1] = "none"
    /\ seq' = [seq EXCEPT ![scanned + 1] = v]
    /\ scanned' = scanned + 1
    /\ candidate' = IF scanned = 0 THEN v
                     ELSE IF candidate = v THEN candidate
                     ELSE Head
    /\ countCand' = IF scanned = 0 THEN 1
                    ELSE IF candidate = v THEN countCand + 1
                    ELSE IF Head = v THEN countCand - 1
                    ELSE countCand
    /\ UNCHANGED concluded

Conclude ==
    /\ concluded = FALSE
    /\ scanned = 3
    /\ concluded' = TRUE
    /\ UNCHANGED <<seq, candidate, scanned, countCand>>

Idle ==
    /\ concluded = TRUE
    /\ UNCHANGED vars

Next ==
    \/ \E v \in Value : ScanValue(v)
    \/ Conclude
    \/ Idle

Spec == Init /\ [][Next]_vars

Inv == candidate # "none" => (2 * countCand > scanned)

Correct == (scanned = 3) => (candidate # "none" /\ Inv)

====