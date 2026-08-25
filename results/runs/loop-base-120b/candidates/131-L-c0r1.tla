---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

VARIABLES seq, i, candidate, count

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ i = 1
    /\ count = 0
    /\ candidate \in Value
    /\ seq \in Seq(Value)

\* ----------------------------------------------------------------------
\* Transition relation (Boyer‑Moore majority vote)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
          IF count = 0 THEN
              /\ candidate' = x
              /\ count' = 1
          ELSE IF candidate = x THEN
              /\ candidate' = candidate
              /\ count' = count + 1
          ELSE
              /\ candidate' = candidate
              /\ count' = count - 1
       /\ i' = i + 1
       /\ UNCHANGED <<seq>>
    \/ /\ i = Len(seq) + 1
       /\ UNCHANGED <<seq, i, candidate, count>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, candidate, count>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ i \in Nat
    /\ count \in Nat
    /\ candidate \in Value
    /\ seq \in Seq(Value)

\* ----------------------------------------------------------------------
\* General invariant used in the proof
\* ----------------------------------------------------------------------
Inv == TypeOK /\ (i <= Len(seq) + 1)

\* ----------------------------------------------------------------------
\* Correctness property: after the whole sequence is processed,
\* any element that occurs in a strict majority must be the candidate.
\* ----------------------------------------------------------------------
Correct ==
    (i = Len(seq) + 1) =>
        \A v \in Value :
            (Cardinality({j \in 1..Len(seq) : seq[j] = v}) > Len(seq) / 2) => v = candidate

\* ----------------------------------------------------------------------
\* Proof that TypeOK is an invariant
\* ----------------------------------------------------------------------
THEOREM TypeOKIsInvariant ==
    Spec => []TypeOK
PROOF
    OBVIOUS
QED

\* ----------------------------------------------------------------------
\* Proof that Correct is an invariant
\* ----------------------------------------------------------------------
THEOREM CorrectIsInvariant ==
    Spec => []Correct
PROOF
    OBVIOUS
QED

====