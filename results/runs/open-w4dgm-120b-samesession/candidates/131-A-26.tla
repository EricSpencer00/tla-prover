---- MODULE MajorityProof ----
EXTENDS MajoritySpec, FiniteSets

CONSTANTS Value

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ candidate \in Value
  /\ candidateCount \in 0..3
  /\ scanned \in 0..3

Inv ==
  /\ candidateCount = Cardinality({i \in 1..scanned : seq[i] = candidate})

Init ==
  /\ seq = << >>
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ candidateCount = 0
  /\ scanned = 0

Append(v) ==
  /\ scanned < 3
  /\ seq' = Append(seq, v)
  /\ scanned' = scanned + 1
  /\ IF scanned = 0 THEN
       /\ candidate' = v
       /\ candidateCount' = 1
     ELSE IF v = candidate THEN
       /\ candidate' = candidate
       /\ candidateCount' = candidateCount + 1
     ELSE IF candidateCount > 1 THEN
       /\ candidate' = candidate
       /\ candidateCount' = candidateCount - 1
     ELSE
       /\ candidate' \in Value
       /\ candidateCount' = 1
  /\ UNCHANGED <<>>

Next ==
  \/ \E v \in Value : Append(v)

Spec == Init /\ [][Next]_<<seq, candidate, candidateCount, scanned>>

Correct ==
  scanned = 3 => \A v \in Value : (2 * Cardinality({i \in 1..3 : seq[i] = v}) > 3) => v = candidate

====