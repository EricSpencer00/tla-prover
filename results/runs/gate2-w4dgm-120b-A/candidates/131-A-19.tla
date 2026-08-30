---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajoritySpec

CONSTANTS Value

VARIABLES seq, scanned, candidate, majority

vars == <<seq, scanned, candidate, majority>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ scanned \in Nat
  /\ candidate \in Value
  /\ majority \in {"None", "CandidateOnly", "CandidateNotOnly"}

Inv ==
  /\ scanned <= Len(seq)
  /\ \A i \in 1..scanned : seq[i] = candidate

Init ==
  /\ seq = << >>
  /\ scanned = 0
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ majority = "None"

Vote(value) ==
  /\ seq' = Append(seq, value)
  /\ UNCHANGED <<scanned, candidate, majority>>

Scan ==
  /\ scanned < Len(seq)
  /\ scanned' = scanned + 1
  /\ candidate' = seq[scanned + 1]
  /\ UNCHANGED <<seq, majority>>

Commit ==
  /\ scanned = Len(seq)
  /\ Len(seq) > 0
  /\ \E v \in Value : candidate' = v
  /\ UNCHANGED <<seq, scanned, majority>>

Decide ==
  /\ majority = "None"
  /\ majority' = IF \A v \in Value : Cardinality({i \in 1..scanned : seq[i] = v}) * 2 <= scanned
                THEN "None"
                ELSE IF Cardinality({i \in 1..scanned : seq[i] = candidate}) * 2 > scanned
                     THEN "CandidateOnly"
                     ELSE "CandidateNotOnly"
  /\ UNCHANGED <<seq, scanned, candidate>>

Reopen ==
  /\ majority # "None"
  /\ scanned' = 0
  /\ majority' = "None"
  /\ UNCHANGED <<seq, candidate>>

Next ==
  \/ \E value \in Value : Vote(value)
  \/ Scan
  \/ Commit
  \/ Decide
  \/ Reopen

Spec == Init /\ [][Next]_vars

Correct ==
  /\ majority \in {"None", "CandidateOnly", "CandidateNotOnly"}
  /\ (majority = "CandidateOnly" => \A v \in Value : Cardinality({i \in 1..scanned : seq[i] = v}) * 2 <= scanned)

====