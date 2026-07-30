---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

ASSUME Value \in SUBSET Nat

VARIABLES seq, candidate, count, i, occ

vars == <<seq, candidate, count, i, occ>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value \cup {0}
  /\ count \in Nat
  /\ i \in 0..Len(seq)
  /\ occ \in [1..Len(seq) -> SUBSET 1..Len(seq)]

Init ==
  /\ seq = <<>>
  /\ candidate = 0
  /\ count = 0
  /\ i = 0
  /\ occ = [v \in 1..Len(seq) |-> {}]

Vote(x) ==
  /\ i < Len(seq)
  /\ LET y == seq[i + 1] IN
       /\ seq' = seq
       /\ candidate' = IF count = 0 THEN y ELSE candidate
       /\ count' = IF count = 0 THEN 1
                    ELSE IF y = candidate THEN count + 1
                    ELSE count - 1
       /\ i' = i + 1
       /\ occ' = [occ EXCEPT ![x] = @ \cup {i + 1}]
  /\ UNCHANGED <<seq, candidate, count>>

InitSeq ==
  /\ UNCHANGED <<seq, candidate, count, i, occ>

Spec == Init /\ [Vote]_vars /\ [InitSeq]_vars

OccBefore(v, k) == {j \in occ[v] : j <= k}

Inv ==
  /\ i <= Len(seq)
  /\ (i = Len(seq) => candidate # 0)
  /\ count >= 1
  /\ \A v \in Value :
       Cardinality(OccBefore(v, i)) <= Cardinality(OccBefore(candidate, i))

Correct ==
  \A v \in Value :
    (v \in occ[candidate] /\ 2 * Cardinality(occ[v]) > Len(seq))
      => v = candidate

====