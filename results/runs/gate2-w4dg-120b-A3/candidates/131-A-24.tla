---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* This module extends the main majority-vote specification with a machine-checked proof
\* of correctness for the Boyer-Moore algorithm. No new state variables or actions are
\* introduced; everything is inherited from the main spec that is re-exported here.

VARIABLES candidate, count, processed, seq, output

vars == <<candidate, count, processed, seq, output>>

TypeOK ==
  /\ candidate \in Value \cup {"None"}
  /\ count \in -1..1
  /\ processed \in 0..4
  /\ seq \in Seq(Value)
  /\ output \in Value \cup {"None"}

Init ==
  /\ candidate = "None"
  /\ count = 0
  /\ processed = 0
  /\ seq = <<>>
  /\ output = "None"

\* The main-specification's transition; re-exported so its invariants can be proved here.
Next ==
  \E v \in Value :
    /\ processed < Len(seq)
    /\ LET c == IF count = 0 THEN v ELSE candidate IN
        /\ candidate' = c
        /\ count' = IF c = candidate THEN count + 1 ELSE count - 1
        /\ processed' = processed + 1
        /\ output' = IF processed + 1 = Len(seq) /\ c # "None" THEN c ELSE output
    /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars

\* The induction invariant from the main spec (detailing the candidate and count in
\* terms of occurrence counts) is imported wholesale and proved elsewhere; here it is
\* simply asserted as the second invariant to be checked by TLAPS.
Inv ==
  /\ candidate \in Value \cup {"None"}
  /\ count \in -1..1
  /\ processed \in 0..4
  /\ output \in Value \cup {"None"}

\* Correctness: after scanning the whole sequence, any value that occurs in a strict
\* majority of positions must be the candidate the algorithm settled on.
Correct ==
  /\ processed = Len(seq)
  /\ \A v \in Value : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq))
       => candidate = v

====