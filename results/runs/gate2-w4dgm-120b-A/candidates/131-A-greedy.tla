---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* No new state; everything is inherited from MajorityVote.

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value \cup {"none"}
  /\ count \in Nat
  /\ scanned \in Nat

\* The inductive invariant from the main spec, restated here for TLAPS.
Inv ==
  /\ scanned <= Len(seq)
  /\ count = Cardinality({i \in 1..Len(seq) : seq[i] = candidate})
  /\ scanned = 0 => candidate = "none"

Init ==
  /\ seq = << >>
  /\ candidate = "none"
  /\ count = 0
  /\ scanned = 0

\* The candidate is only ever set while count is zero, so it stays the
\* unique element with a strict majority of the scanned prefix.
Vote(v) ==
  /\ scanned < Len(seq)
  /\ seq' = seq
  /\ candidate' = IF count = 0 THEN v ELSE candidate
  /\ count' = IF count = 0 THEN 1 ELSE IF v = candidate THEN count + 1 ELSE count
  /\ scanned' = scanned + 1

Next == \E v \in Value : Vote(v)

Spec == Init /\ [][Next]_<<seq, candidate, count, scanned>>

\* The candidate is the only value that can hold a strict majority of the
\* whole sequence once the scan is complete.
Correct ==
  /\ scanned = Len(seq)
  /\ \A v \in Value : (Cardinality({i \in 1..Len(seq) : seq[i] = v}) * 2 > Len(seq)) => v = candidate

====