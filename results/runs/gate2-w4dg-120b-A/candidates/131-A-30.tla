---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* Action symbols used in the main majority vote algorithm (imported but
\* re-declared here so the module is self-contained).
AInit == "Init"
ARead == "Read"
AInc == "Inc"
AEvict == "Evict"
AEmit == "Emit"

\* State variables: exactly the same as in the main algorithm.
Vars == << seq, count, candidate, status, out >>

\* seq: the input sequence of values; count: votes for the current candidate;
\* candidate: the current majority candidate; status: scanning or done; out:
\* the final output.
TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ count \in 0..3
  /\ candidate \in Value
  /\ status \in {"scanning", "done"}
  /\ out \in Value \cup {"none"}

Init ==
  /\ seq \in [1..3 -> Value]
  /\ count = 0
  /\ candidate \in Value
  /\ status = "scanning"
  /\ out = "none"

Read ==
  /\ status = "scanning"
  /\ status' = "scanning"
  /\ UNCHANGED << seq, count, candidate, out >>

Inc(v) ==
  /\ status = "scanning"
  /\ v = candidate
  /\ count < 3
  /\ count' = count + 1
  /\ UNCHANGED << seq, candidate, status, out >>

Evict(v) ==
  /\ status = "scanning"
  /\ v # candidate
  /\ count > 0
  /\ count' = count - 1
  /\ UNCHANGED << seq, candidate, status, out >>

Emit ==
  /\ status = "scanning"
  /\ status' = "done"
  /\ out' = candidate
  /\ UNCHANGED << seq, count, candidate >>

Next ==
  \/ Read
  \/ \E v \in Value : Inc(v)
  \/ \E v \in Value : Evict(v)
  \/ Emit

Spec == Init /\ [][Next]_Vars

\* Correctness invariant: after scanning the whole sequence, any value that
\* occurs in a strict majority of positions must equal the candidate.
Correct ==
  (status = "done") =>
    (\A a \in Value : (2 * Cardinality({i \in 1..3 : seq[i] = a}) > 3) => a = candidate)

====