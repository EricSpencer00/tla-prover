---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* ----------------------------------------------------------------------
\* State variables (inherited from the main majority‑vote specification)
\* ----------------------------------------------------------------------
VARIABLES seq, i, candidate, count

\* ----------------------------------------------------------------------
\* Initialization (same as in the main specification)
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in Seq(Value)                \* the input sequence of values
    /\ i = 0                              \* index of the next element to read
    /\ candidate \in Value                \* current candidate (arbitrary)
    /\ count = 0

\* ----------------------------------------------------------------------
\* Transition relation (the Boyer‑Moore voting step)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ i < Len(seq)                    \* there are still elements to scan
       /\ LET v == seq[i + 1] IN
          IF count = 0 THEN
              /\ candidate' = v
              /\ count' = 1
          ELSE IF v = candidate THEN
              /\ candidate' = candidate
              /\ count' = count + 1
          ELSE
              /\ candidate' = candidate
              /\ count' = count - 1
       /\ i' = i + 1
       /\ UNCHANGED <<seq>>
    \/ /\ i = Len(seq)                    \* scanning finished, stutter
       /\ UNCHANGED <<seq, i, candidate, count>>

\* ----------------------------------------------------------------------
\* Specification of the whole system
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<|seq, i, candidate, count|>

\* ----------------------------------------------------------------------
\* Invariant: type correctness of all state components
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in Nat
    /\ candidate \in Value
    /\ count \in Nat

\* ----------------------------------------------------------------------
\* Invariant used in the main specification (inductive invariant)
\* ----------------------------------------------------------------------
Inv ==
    /\ i <= Len(seq)
    /\ (count = 0 => candidate \in Value)   \* trivial guard

\* ----------------------------------------------------------------------
\* Correctness invariant: after the whole sequence is processed,
\* any value that appears in a strict majority must be the final candidate.
\* ----------------------------------------------------------------------
Correct ==
    /\ i = Len(seq)
    /\ \A v \in Value :
          (Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2)
          => v = candidate

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS == TypeOK, Correct, Inv

====