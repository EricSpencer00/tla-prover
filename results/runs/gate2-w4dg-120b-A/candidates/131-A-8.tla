---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets
CONSTANTS Value

CONSTANT MaxN

VARIABLES seq, candidate, count, index

vars == <<seq, candidate, count, index>>

PositionsBefore(i) == {k \in 0 .. (i - 1) : seq[k] = candidate}

TypeOK ==
  /\ seq \in [0 .. (MaxN - 1) -> Value]
  /\ candidate \in Value
  /\ count \in Nat
  /\ index \in 0 .. MaxN

Init ==
  /\ candidate \in Value
  /\ count = 0
  /\ index = 0

Next ==
  \/ /\ index < MaxN
     /\ LET x == seq[index] IN
          /\ candidate' = IF count = 0 THEN x ELSE candidate
          /\ count' = IF count = 0 THEN 1 ELSE IF x = candidate THEN count + 1 ELSE count - 1
     /\ index' = index + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars

Inv ==
  /\ (index = MaxN) => (cardinality(PositionsBefore(index)) > index \div 2 => candidate = seq[index - 1])
  /\ (count >= 1) => (candidate \in Value)

Correct == (index = MaxN) => (cardinality(PositionsBefore(index)) > index \div 2 => candidate = seq[index - 1])

====