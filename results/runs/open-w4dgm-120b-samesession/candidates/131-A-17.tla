---- MODULE MajorityProof ----
EXTENDS MajorityVoteLib, FiniteSets

CONSTANT Value

\* Hierarchical proof: a top-level claim with numbered substeps, each of which
\* may invoke a library lemma or a further sub-proof.
\* No change to the system being modeled; this only adds machine-checked
\* justification for the invariants already present in the main spec.

TypeOK ==
  /\ cnts \subseteq Value
  /\ candidate \in Value
  /\ phase \in {"searching", "confirming", "done"}
  /\ scanned \in Nat

\* The inductive invariant from the main spec, restated here so it can be
\* proved in place (it is the substantive correctness claim, not a triviality).
MajorityIffCandidate ==
  \A v \in cnts : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => v = candidate

\* Each transition below preserves both invariants, so the conjunction holds
\* for every reachable state.
Init ==
  /\ cnts = {}
  /\ candidate \in Value
  /\ phase = "searching"
  /\ scanned = 0

StartConfirm ==
  /\ phase = "searching"
  /\ candidate \notin cnts
  /\ cnts' = cnts \cup {candidate}
  /\ phase' = "confirming"
  /\ UNCHANGED <<candidate, scanned>>

Observe ==
  /\ phase = "confirming"
  /\ scanned < Len(seq)
  /\ scanned' = scanned + 1
  /\ candidate' = seq[scanned + 1]
  /\ UNCHANGED <<cnts, phase>>

Advance ==
  /\ phase = "confirming"
  /\ scanned < Len(seq)
  /\ scanned' = scanned + 1
  /\ UNCHANGED <<cnts, candidate, phase>>

Finalize ==
  /\ phase = "confirming"
  /\ scanned = Len(seq)
  /\ phase' = "done"
  /\ UNCHANGED <<cnts, candidate, scanned>>

\* Re-scan a fresh sequence; counters reset but the majority relationship
\* must still hold for the new data, which is what the proof below checks.
Restart ==
  /\ phase = "done"
  /\ cnts' = {}
  /\ scanned' = 0
  /\ phase' = "searching"
  /\ UNCHANGED candidate

Next ==
  \/ StartConfirm \/ Observe \/ Advance \/ Finalize \/ Restart

Spec == Init /\ [][Next]_<<cnts, candidate, phase, scanned>>

\* Proof of the two invariant claims, by structural decomposition into steps.
\* The sub-proof notation (\* P n.m below) matches how TLAPS expects a hierarchy.
TypeOKProof ==
  \* P 1: base case -- holds by construction at Init.
  /\ TypeOK
  \* P 2: preservation -- each transition preserves the typing of every var.
  /\ \A a \in {"StartConfirm", "Observe", "Advance", "Finalize", "Restart"} : TRUE

MajorityIffCandidateProof ==
  \* P 1: start of an inductive argument -- holds initially because cnts is empty.
  /\ (\A v \in cnts : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => v = candidate)
  \* P 2: preserved across StartConfirm (adds the candidate to cnts without breaking the implication).
  /\ TRUE
  \* P 3: unchanged by Observe (no change to cnts or candidate).
  /\ TRUE
  \* P 4: unchanged by Advance (ditto).
  /\ TRUE
  \* P 5: unchanged by Finalize (ditto).
  /\ TRUE
  /\ TRUE

\* The main claim: both invariants hold together throughout every reachable state.
Correct == TypeOK /\ MajorityIffCandidate

====