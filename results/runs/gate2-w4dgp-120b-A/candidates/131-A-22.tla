---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

ASSUME Value # {}

VARIABLES seq, i, candidate, count

vars == <<seq, i, candidate, count>>

Positions(j) == {k \in 0..(j - 1) : seq[k] = candidate}

TypeOK ==
  /\ seq \in [0..5 -> Value]
  /\ i \in 0..6
  /\ candidate \in Value
  /\ count \in 0..6

Inv ==
  /\ i <= Len(seq)
  /\ (count = 0 => candidate \in Value)

Init ==
  /\ seq = [k \in 0..5 |-> CHOOSE v \in Value : TRUE]
  /\ i = 0
  /\ candidate \in Value
  /\ count = 0

Vote ==
  /\ i < Len(seq)
  /\ LET s == seq[i] IN
       IF count = 0
         THEN candidate' = s /\ count' = 1
         ELSE IF s = candidate
                THEN candidate' = candidate /\ count' = count + 1
                ELSE candidate' = candidate /\ count' = count - 1
  /\ i' = i + 1

Reset ==
  /\ i = Len(seq)
  /\ i' = 0
  /\ count' = 0
  /\ UNCHANGED <<seq, candidate>>

Next == Vote \/ Reset

Spec == Init /\ [][Next]_vars

TypeOKInv == TypeOK

Correct ==
  (i = Len(seq) /\ count > 0) => (2 * Cardinality(Positions(Len(seq))) > Len(seq))

====