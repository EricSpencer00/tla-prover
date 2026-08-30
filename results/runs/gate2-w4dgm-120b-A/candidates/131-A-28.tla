---- MODULE MajorityProof ----
EXTENDS MajoritySpec, FiniteSets

CONSTANTS Value

VARIABLES seq, candidate, phase, scanned, checked

vars == <<seq, candidate, phase, scanned, checked>>

Init ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value
  /\ phase = "voting"
  /\ scanned = 0
  /\ checked = {}

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value
  /\ phase \in {"voting", "decided"}
  /\ scanned \in Nat
  /\ checked \subseteq Nat

Vote ==
  /\ phase = "voting"
  /\ scanned < Len(seq)
  /\ phase' = IF seq[scanned + 1] = candidate THEN "voting" ELSE phase
  /\ scanned' = scanned + 1
  /\ UNCHANGED <<seq, candidate, checked>>

Decide ==
  /\ phase = "voting"
  /\ scanned = Len(seq)
  /\ phase' = "decided"
  /\ UNCHANGED <<seq, candidate, scanned, checked>>

CheckOcc ==
  /\ phase = "decided"
  /\ \E i \in 1..Len(seq) :
       /\ i \notin checked
       /\ checked' = checked \cup {i}
  /\ UNCHANGED <<seq, candidate, phase, scanned>>

Sort ==
  /\ phase = "decided"
  /\ Len(seq) > 0
  /\ seq' = <<candidate>>
  /\ scanned' = 1
  /\ UNCHANGED <<candidate, phase, checked>>

Next == Vote \/ Decide \/ CheckOcc \/ Sort

Spec == Init /\ [][Next]_vars

Inv ==
  /\ TypeOK
  /\ Cardinality(checked) * 2 > Len(seq) => seq[scanned] = candidate

Correct ==
  /\ TypeOK
  /\ (scanned = Len(seq) /\ Inv)

====