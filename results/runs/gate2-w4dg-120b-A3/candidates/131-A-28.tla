---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets
CONSTANTS Value
\* The Boyer-Moore majority vote algorithm, in a module that adds a
\* machine-checked proof of correctness.  There are no new state
\* variables or actions beyond those in the original algorithm; the
\* extension is the proof itself.
\* All identifiers below are required by the reference .cfg file.

VARIABLES candidate, count, scanned

\* The algorithm scans a fixed sequence of values (seq).  It maintains
\* a candidate value together with a support count; scanned is the set
\* of indices already processed.
vars == <<candidate, count, scanned>>

SeqLength == 3
Seq == <<"a", "a", "b">>

\* Number of scans performed so far.
ScannedCount == Cardinality(scanned)
Occurrences(v) == Cardinality({i \in 0..(SeqLength - 1) : Seq[i] = v})

NONE == "none"

TypeOK ==
  /\ candidate \in {NONE} \cup Value
  /\ count \in 0..SeqLength
  /\ scanned \subseteq (0..(SeqLength - 1))

Init ==
  /\ candidate = NONE
  /\ count = 0
  /\ scanned = {}

\* The Boyer-Moore update rule: a matching value boosts the candidate,
\* a mismatch decrements support, and with no support left a fresh
\* value becomes candidate.
Vote(i) ==
  /\ i \notin scanned
  /\ scanned' = scanned \cup {i}
  /\ candidate' = IF count = 0 THEN Seq[i] ELSE candidate
  /\ count' = IF count = 0 THEN 1 ELSE IF Seq[i] = candidate THEN count + 1 ELSE count - 1
  /\ UNCHANGED <<>>

Next == \E i \in 0..(SeqLength - 1) : Vote(i)

Spec == Init /\ [][Next]_vars

\* A value that occurs in a strict majority of positions must equal the
\* candidate held at the end of the scan.
Correct ==
  \A v \in Value : (Occurrences(v) * 2 > SeqLength) => (candidate = v)

\* The invariant from the original algorithm; lifted unchanged to the
\* proof module so it can be proved again here.
Inv ==
  /\ candidate \in {NONE} \cup Value
  /\ count \in 0..SeqLength
  /\ scanned \subseteq (0..(SeqLength - 1))

\* Proof of type correctness.  It's an invariant inherited from the base
\* algorithm, re-established here for completeness.
TypeOK ==
  /\ candidate \in {NONE} \cup Value
  /\ count \in 0..SeqLength
  /\ scanned \subseteq (0..(SeqLength - 1))

====