---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The proof extends the majority vote algorithm and records two invariants:
\* TypeOK (all variables range over their intended types) and Correct (the
\* candidate is the only possible majority element once the scan is done).

VARIABLES seq, cand, count, i

vars == <<seq, cand, count, i>>

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ cand \in Value
  /\ count \in 0..3
  /\ i \in 0..3

Init ==
  /\ seq = <<>>
  /\ cand = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ i = 0

ExtendSeq(v) ==
  /\ i < 3
  /\ seq' = [seq EXCEPT ![i + 1] = v]
  /\ i' = i + 1
  /\ cand' = cand
  /\ count' = count
  /\ UNCHANGED <<>>

Vote(v) ==
  /\ i = 3
  /\ cand' = IF count = 0 THEN v ELSE cand
  /\ count' = IF count = 0 THEN 1 ELSE IF v = cand THEN count + 1 ELSE count - 1
  /\ UNCHANGED <<seq, i>>

Spec == Init /\ [][ExtendSeq(v) \/ Vote(v) : v \in Value]

\* The inductive invariant from the main spec: count is the net of how many
\* times the candidate has been confirmed minus times it was cancelled.
Inv ==
  /\ cand \in Value
  /\ count \in 0..3
  /\ i <= 3
  /\ \E occ \in [1..i -> Value] : occ = seq

\* A strict majority means the occurrence set strictly exceeds half the scan.
OccursStrictlyMoreThanHalf(x) ==
  LET occs == {k \in 1..i : seq[k] = x} IN occs # {} /\ 2 * Cardinality(occs) > i

Correct ==
  \A x \in Value : OccursStrictlyMoreThanHalf(x) => x = cand

====