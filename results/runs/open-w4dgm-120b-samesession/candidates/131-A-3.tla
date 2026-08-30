---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANT Value

VARIABLES seq, scanned, candidate, supported, active

vars == <<seq, scanned, candidate, supported, active>>
Total == 3

TypeOK ==
  /\ seq \in [1..Total -> Value \cup {"none"}]
  /\ scanned \in 0..Total
  /\ candidate \in Value \cup {"none"}
  /\ supported \in 0..Total
  /\ active \in BOOLEAN

Init ==
  /\ seq = [i \in 1..Total |-> "none"]
  /\ scanned = 0
  /\ candidate = "none"
  /\ supported = 0
  /\ active = TRUE

WriteValue(v) ==
  /\ scanned < Total
  /\ active
  /\ seq' = [seq EXCEPT ![scanned + 1] = v]
  /\ scanned' = scanned + 1
  /\ candidate' = IF scanned = 0 THEN v ELSE candidate
  /\ supported' = IF scanned = 0 THEN 1
                   ELSE IF v = candidate THEN supported + 1 ELSE supported
  /\ UNCHANGED active

ToggleActive ==
  /\ active' = ~active
  /\ UNCHANGED <<seq, scanned, candidate, supported>>

Next == \E v \in Value : WriteValue(v) \/ ToggleActive

Spec == Init /\ [][Next]_vars
Inv == /\ scanned <= Total
        /\ supported <= scanned
        /\ (candidate = "none" <=> scanned = 0)

TypeOKInv == TypeOK /\ Inv

Correct ==
  /\ Inv
  /\ scanned = Total
  /\ supported * 2 > Total
  /\ \A i \in 1..Total : seq[i] = candidate

====