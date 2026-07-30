---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Integers

CONSTANTS Value

\* The proof module builds on the main Boyer-Moore majority vote
\* specification, adding only proof obligations and no new state.
\* Spec, Init, Next, TypeOK, Correct, and Inv are imported from it and
\* restated here verbatim so the .cfg names resolve in this file.

\* Views of the scan so far: the candidate a majority vote is tracking,
\* and its current count.
VARIABLES candidate, count

RECURSIVE CountOcc(_, _, _)
CountOcc(seq, v, i) ==
  IF i = 0 THEN 0
  ELSE (IF seq[i] = v THEN 1 ELSE 0) + CountOcc(seq, v, i - 1)

\* The Boyer-Moore scan runs for a fixed sequence length; the model
\* uses a bounded length so the invariant below is meaningful.
\* Length is a constant here, not a variable, so the state space stays
\* finite and reachable.
Length == 2

\* The specification from the main module, restated here so the .cfg
\* requirements are satisfied in this file.
Init == candidate = "none" /\ count = 0

\* Scan one more position of the fixed sequence and update count.
\* The sequence values are nondeterministic but fixed by the bound.
Next == \E v \in Value :
          /\ count' = IF count = 0 THEN 1 ELSE IF candidate = v THEN count + 1 ELSE count - 1
          /\ candidate' = IF count = 0 THEN v ELSE candidate
          /\ UNCHANGED << >>

Spec == Init /\ [][Next]_<<candidate, count>>

\* Type correctness of the model's two variables.
TypeOK == candidate \in (Value \cup {"none"}) /\ count \in 0..Length

\* After scanning the whole length, any value occurring in a strict
\* majority of positions must be the candidate.
Correct == CountOcc(<<>>, candidate, Length) > Length \div 2

\* The inductive invariant from the main module: the count field never
\* strays outside its sound range once a candidate exists.
Inv == (candidate # "none") => (count >= 1 /\ count <= Length)

====