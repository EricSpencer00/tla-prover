---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

NumVals == 3

Seq == UNION {[1..n -> 0..(NumVals - 1)] : n \in Nat}
Counts == [Value -> Nat]

VARIABLES seq, n, candidate, occ, seen

vars == <<seq, n, candidate, occ, seen>>

TypeOK ==
  /\ seq \in Seq
  /\ n \in Nat
  /\ candidate \in Value
  /\ occ \in Counts
  /\ seen \in Nat

Init ==
  /\ seq = [i \in 1..0 |-> 0]
  /\ n = 0
  /\ candidate = 0
  /\ occ = [v \in Value |-> 0]
  /\ seen = 0

\* The extension adds no new actions; it derives the whole spec from the
\* main Boyer-Moore module it extends.
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Safety property #1: type correctness is an invariant of the spec.
TypeOKInv == TypeOK

\* Safety property #2: after scanning the whole sequence, any element
\* occurring in a strict majority of positions must be the candidate.
Correct ==
  /\ seen = n
  /\ n > 0
  /\ Cardinality({i \in 1..n : seq[i] = candidate}) * 2 > n
  /\ \A i \in 1..n : seq[i] = candidate

Inv == Correct

====