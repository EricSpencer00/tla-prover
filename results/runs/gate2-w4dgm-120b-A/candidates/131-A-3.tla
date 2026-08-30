---- MODULE MajorityProof ----
EXTENDS Integers, Sequences, FiniteSets, MajorityVote

CONSTANTS Value

Spec == MajoritySpec

Init == MajorityInit

Next == MajorityNext

TypeOK ==
  /\ seq \in Seq(Value)
  /\ n \in Nat
  /\ pos \in Nat
  /\ candidate \in Value
  /\ candidateSet \subseteq Value
  /\ Count == [v \in Value |-> Cardinality({i \in 1..Len(seq) : seq[i] = v})]

\* The standard Boyer-Moore candidate always survives past a strict majority.
Correct == (candidate \in candidateSet) /\ (2 * Count[candidate] > Len(seq))

Inv == TypeOK /\ Correct

vars == {seq, n, pos, candidate, candidateSet}
====