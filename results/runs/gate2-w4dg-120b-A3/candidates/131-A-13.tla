---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

VARIABLES seq, pos, candidate, count, scanCount

vars == <<seq, pos, candidate, count, scanCount>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ pos \in 0..Len(seq)
  /\ candidate \in Value
  /\ count \in 0..Len(seq)
  /\ scanCount \in 0..Len(seq)

Init ==
  /\ seq = <<>>
  /\ pos = 0
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ scanCount = 0

Assign(v) ==
  /\ pos < Len(seq)
  /\ seq' = [seq EXCEPT ![pos] = v]
  /\ pos' = pos + 1
  /\ UNCHANGED <<candidate, count, scanCount>>

Vote(v) ==
  /\ count = 0
  /\ candidate' = v
  /\ count' = 1
  /\ UNCHANGED <<seq, pos, scanCount>>

Agree(v) ==
  /\ count > 0
  /\ candidate = v
  /\ count' = count + 1
  /\ UNCHANGED <<seq, pos, candidate, scanCount>>

Disagree(v) ==
  /\ count > 0
  /\ candidate # v
  /\ count' = count - 1
  /\ UNCHANGED <<seq, pos, candidate, scanCount>>

Scan ==
  /\ pos = Len(seq)
  /\ scanCount < Len(seq)
  /\ scanCount' = scanCount + 1
  /\ UNCHANGED <<seq, pos, candidate, count>>

Next ==
  \/ \E v \in Value : Assign(v)
  \/ \E v \in Value : Vote(v)
  \/ \E v \in Value : Agree(v)
  \/ \E v \in Value : Disagree(v)
  \/ Scan
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Correct ==
  /\ pos = Len(seq)
  /\ scanCount = Len(seq)
  /\ \A v \in Value :
       (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => v = candidate

====