---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT Value \* the (non‑empty) set of possible values in the input stream

\* ----------------------------------------------------------------------
\* Helper definitions (imported from the main majority vote spec)
\* ----------------------------------------------------------------------
\* For the purposes of this self‑contained module we re‑declare the
\* essential parts of the original majority‑vote algorithm.
VARIABLES seq, i, cand, cnt

\* The input sequence is a finite sequence of values drawn from Value.
Seq == seq

\* Index i points to the next element to process (1..Len(seq)+1).
\* cand holds the current candidate, cnt the associated counter.
\* The algorithm starts with i = 1, cnt = 0, cand arbitrary.
Init ==
    /\ i = 1
    /\ cnt = 0
    /\ cand \in Value
    /\ seq \in [1..Len(seq) -> Value]

\* One step of the Boyer‑Moore algorithm.
Next ==
    \/ /\ i <= Len(seq)
       /\ IF cnt = 0
          THEN /\ cand' = seq[i]
               /\ cnt' = 1
          ELSE IF seq[i] = cand
               THEN /\ cand' = cand
                    /\ cnt' = cnt + 1
               ELSE /\ cand' = cand
                    /\ cnt' = cnt - 1
       /\ i' = i + 1
    \/ /\ i > Len(seq)      \* stutter after the scan is finished
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* The overall specification.
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in [1..Len(seq) -> Value]
    /\ i \in Nat
    /\ cand \in Value
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Helper function: occurrence count of a value up to a given index
\* ----------------------------------------------------------------------
Occur(v, k) == Cardinality({j \in 1..k : seq[j] = v})

\* ----------------------------------------------------------------------
\* Correctness invariant (Inv) – the core of the majority proof
\* ----------------------------------------------------------------------
\* For any value v that appears in more than half of the processed
\* prefix (i‑1 elements), v must be the current candidate.
Inv ==
    \A v \in Value :
        (Occur(v, i-1) > (i-1) / 2) => (cand = v)

\* ----------------------------------------------------------------------
\* Main correctness property (Correct) – after the whole sequence is
\* processed, any strict majority value equals the final candidate.
\* ----------------------------------------------------------------------
Correct ==
    i > Len(seq) => \A v \in Value :
        (Occur(v, Len(seq)) > Len(seq) / 2) => (cand = v)

\* ----------------------------------------------------------------------
\* The theorem stating that the specification satisfies the invariants
\* ----------------------------------------------------------------------
THEOREM SpecImpliesInv == Spec => []Inv

\* ----------------------------------------------------------------------
\* The theorem stating that the specification satisfies the correctness
\* property
\* ----------------------------------------------------------------------
THEOREM SpecImpliesCorrect == Spec => []Correct

====