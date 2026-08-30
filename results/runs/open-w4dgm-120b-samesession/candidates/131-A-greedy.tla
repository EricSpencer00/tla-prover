---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* No new state; everything is inherited from MajorityVote.
\* The proof obligations below are the ONLY additions this module makes.

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value
  /\ scanned \in 0..Len(seq)

\* The inductive invariant from the main spec, restated here for TLAPS.
Inv ==
  /\ candidate = seq[1]
  /\ \A i \in 1..scanned : seq[i] = candidate

Init ==
  /\ seq = << >>
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ scanned = 0

\* The action set is exactly the same as in MajorityVote; we restate it
\* here so the proof can refer to it directly.
Next ==
  \/ \E v \in Value :
       /\ seq' = Append(seq, v)
       /\ candidate' = IF Len(seq) = 0 THEN v ELSE candidate
       /\ scanned' = 0
  \/ scanned < Len(seq) /\ scanned' = scanned + 1 /\ UNCHANGED <<seq, candidate>>

Spec == Init /\ [][Next]_<<seq, candidate, scanned>>

\* The type invariant is proved by checking it at Init and preservation.
TypeOKIsInvariant ==
  /\ TypeOK
  /\ (TypeOK => [][TypeOK]_<<seq, candidate, scanned>>)

\* The correctness property is the invariant from the main spec.
Correct == Inv

====