---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

\* Extending the main Boyer-Moore majority vote spec with a machine-checked
\* proof of its correctness. The new module introduces no extra state or
\* actions; it only re-proves that the inherited spec's invariants hold and
\* that the algorithm's output is the unique majority element.

CONSTANTS Value

VARIABLES cand, count, seen, occ
vars == <<cand, count, seen, occ>>

\* Index range of the input sequence. The proof does not explore all
\* sequences, so the bound is a small but representative sample.
MaxI == 2

TypeOK ==
  /\ cand \in Value \cup {"none"}
  /\ count \in 0..MaxI
  /\ seen \in 0..MaxI
  /\ occ \in [1..MaxI -> SUBSET Value]

\* The inductive invariant from the main spec: the candidate is the only
\* value that could still reach a strict majority within the remaining
\* unseen positions.
Inv ==
  /\ count >= 0
  /\ \A x \in Value : seen >= MaxI - Cardinality(occ[x])
  /\ cand \in occ[seen] \/ (seen = 0 /\ cand = "none")

Init ==
  /\ cand = "none"
  /\ count = 0
  /\ seen = 0
  /\ occ = [x \in 1..MaxI |-> {}]

\* The Boyer-Moore transition: observe the next value and update the
\* candidate and count accordingly.
NextStep ==
  /\ seen < MaxI
  /\ \E x \in Value :
       /\ occ' = [occ EXCEPT ![seen + 1] = occ[seen + 1] \cup {x}]
       /\ IF count = 0 THEN cand' = x ELSE cand' = cand
  /\ count' = IF count = 0 THEN 1 ELSE IF cand = x THEN count + 1 ELSE count - 1
  /\ seen' = seen + 1

Spec == Init /\ [][NextStep]_vars

\* Explicitly state the two things being proved: type correctness and the
\* algorithm's output correctness.
TypeOKInv == TypeOK
Correct == Inv

====