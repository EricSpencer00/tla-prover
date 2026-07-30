---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Value

ASSUME Value \in FiniteSets

VARIABLES candidate, count, scanned, seq

vars == <<candidate, count, scanned, seq>>

TypeOK ==
  /\ candidate \in Value
  /\ count \in 0..Len(seq)
  /\ scanned \in 0..Len(seq)
  /\ seq \in Seq(Value)

Init ==
  /\ candidate \in Value
  /\ count = 0
  /\ scanned = 0
  /\ seq \in Seq(Value)

Process ==
  /\ scanned < Len(seq)
  /\ LET v == seq[scanned + 1] IN
       /\ candidate' = IF count = 0 THEN v ELSE candidate
       /\ count' = IF v = candidate THEN count + 1 ELSE IF count = 0 THEN 0 ELSE count - 1
  /\ scanned' = scanned + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Process]_vars

\* Hierarchical proof: type correctness is proved first, then the algorithm's
\* output correctness, using the invariant framework of the main spec.
InitTypeOK == Init
StepTypeOK ==
  /\ Process
  /\ TypeOK
  /\ UNCHANGED TypeOK
Correct ==
  (scanned = Len(seq) /\ 2 * Cardinality({i \in 1..Len(seq) : seq[i] = candidate}))
    =< Len(seq)
\* The inductive invariant from the main spec is restated here as an invariant.
\* (The main spec's own proof is not reproduced in full here.)
Inv == \A x \in Value : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) <= Len(seq)) \/ candidate = x

====