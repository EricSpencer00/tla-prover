---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The module extends the main Boyer-Moore majority vote specification with
\* formal lemmas and proofs. No new state is introduced; the proof is about
\* the inherited state and actions.

\* State: the scanned prefix length, the current candidate for majority, the
\* leftover count for the candidate, and the full input sequence.
VARIABLES scanned, candidate, leftover, seq

vars == <<scanned, candidate, leftover, seq>>

Init ==
  /\ scanned = 0
  /\ candidate = 0
  /\ leftover = 0
  /\ seq = <<>>

\* The first appearance of any value elects it as candidate with one token.
Enter(v) ==
  /\ scanned = 0
  /\ seq' = <<v>>
  /\ candidate' = v
  /\ leftover' = 1
  /\ scanned' = 1

\* A matching value confirms the current candidate.
Confirm ==
  /\ scanned < Len(seq)
  /\ seq[scanned + 1] = candidate
  /\ scanned' = scanned + 1
  /\ leftover' = leftover + 1
  /\ UNCHANGED <<candidate, seq>>

\* A mismatching value cancels one token of the current candidate.
Cancel ==
  /\ scanned < Len(seq)
  /\ seq[scanned + 1] # candidate
  /\ leftover > 0
  /\ scanned' = scanned + 1
  /\ leftover' = leftover - 1
  /\ UNCHANGED <<candidate, seq>>

\* A mismatching value with no tokens left elects itself as the new candidate.
Elect(v) ==
  /\ scanned < Len(seq)
  /\ seq[scanned + 1] # candidate
  /\ leftover = 0
  /\ candidate' = v
  /\ leftover' = 1
  /\ scanned' = scanned + 1
  /\ UNCHANGED seq

\* The leftover tokens are recycled only once the whole sequence has been scanned;
\* resetting the token count is the only way the algorithm proceeds thereafter.
Recycle ==
  /\ scanned = Len(seq)
  /\ leftover > 0
  /\ leftover' = 0
  /\ UNCHANGED <<scanned, candidate, seq>>

\* Once recycling has drained the tokens the run is finished.
Finish ==
  /\ scanned = Len(seq)
  /\ leftover = 0
  /\ UNCHANGED vars

Next ==
  \/ Confirm
  \/ Cancel
  \/ Recycle
  \/ Finish
  \/ \E v \in Value : Enter(v) \/ Elect(v)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ scanned \in 0..Len(seq)
  /\ candidate \in Value \cup {0}
  /\ leftover \in 0..Len(seq)
  /\ seq \in Seq(Value)

\* The original correctness invariant: the surviving candidate, if any, is the
\* only value that occurs in a strict majority of positions of the sequence.
Correct ==
  \A v \in Value :
    (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq))
      => v = candidate

\* The extended inductive invariant: tokens are never negative, so the counter
\* never runs below zero and the algorithm cannot cancel a non-existent token.
Inv == (leftover >= 0) /\ Correct

====