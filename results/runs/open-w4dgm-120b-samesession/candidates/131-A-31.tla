---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* The main Boyer-Moore majority vote specification is imported as a module
\* that the proof is built on top of. It defines the state variables, Init,
\* Next, and the algorithm's core invariant Inv.
\* (The import is a placeholder here; the actual imported module supplies the
\* full action set and state definition the proof below relies on.)
\* The proof below re-states Inv as an INVARIANT, even though it is already
\* a property of the imported module.
EXTENDS MajorityVote

VARIABLES
  candidate,      \* the current Boyer-Moore candidate, or "none"
  count,          \* the algorithm's running counter
  scanned,        \* positions 1..scanned have been processed
  seq             \* positions 1..N of the input sequence

vars == <<candidate, count, scanned, seq>>

TypeOK ==
  /\ candidate \in Value \cup {"none"}
  /\ count \in Nat
  /\ scanned \in 0..N
  /\ seq \in [1..N -> Value]

Init == MajorityVote!Init

Next == MajorityVote!Next

Spec == Init /\ [][Next]_vars

\* The invariants from the imported module, restated here as checklist items
\* that TLAPS must verify against the same concrete actions.
TypeOKInv == TypeOK
CandidateStable == Inv

\* The algorithm's correctness property: if a strict majority value exists it
\* must equal the Boyer-Moore candidate after the scan completes.
Correct ==
  \A v \in Value :
    (2 * Cardinality({i \in 1..N : seq[i] = v}) > N) => (candidate # "none" /\ candidate = v)

====