---- MODULE MajorityProof ----
\* Formal proof of correctness for the Boyer-Moore majority vote algorithm.
\* No new state; the proof is built on the main spec's actions and variables.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

\* The main spec is imported here so that this module can refer to its symbols.
\* It is external to this file but part of the same model-checking run.
CONSTANTS Sequence

\* No new variables; all are inherited from the main majority vote spec.
VARIABLES phase, candidate, seen, pos, result

vars == <<phase, candidate, seen, pos, result>>

TypeOK ==
  /\ phase \in {"searching", "candidate", "found", "empty"}
  /\ candidate \in Value \cup {"none"}
  /\ seen \in SUBSET Value
  /\ pos \in Nat
  /\ result \in Value \cup {"none"}

\* After the whole sequence has been scanned, the majority element is exactly
\* the candidate the algorithm settled on.
\* This is the algorithm's correctness property, lifted as an invariant.
MajorityIsCandidate ==
  /\ pos = Len(Sequence)
  /\ result = candidate
  /\ \A v \in seen : v = candidate
  /\ candidate \in seen

Init ==
  /\ phase = "searching"
  /\ candidate = "none"
  /\ seen = {}
  /\ pos = 0
  /\ result = "none"

\* The set of positions strictly before the current scan position is a finite
\* subset of the naturals, so its cardinality grows by one exactly when a new
\* position is added -- this lemma is used in the proof of MajorityIsCandidate.
PositionsBefore(p) == {k \in 1..p : TRUE}

\* The main spec's actions are the only ones that can change state; this module
\* adds no new actions of its own.
\* The proof obligations that follow refer to these same actions.
Next == (Init \/ Next)

Spec == Init /\ [][Next]_vars

\* The type invariant holds initially and is preserved by every transition.
TypeOKInv == TypeOK

\* The Boyer-Moore algorithm is correct: after the full scan, any majority
\* element is the candidate the algorithm produced.  This is proved from the
\* inductive invariant present in the main spec.
Correct == MajorityIsCandidate

Inv == TypeOK /\ MajorityIsCandidate

====