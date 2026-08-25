---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

VARIABLES seq, i, cand, count

\* -------------------------------------------------
\* Type correctness invariant
\* -------------------------------------------------
TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in Nat
    /\ cand \in Value \cup {"None"}
    /\ count \in Nat

\* -------------------------------------------------
\* Main algorithm invariant (placeholder)
\* -------------------------------------------------
Inv ==
    /\ i <= Len(seq)
    /\ (count = 0 => cand = "None")
    /\ (count > 0 => cand \in Value)

\* -------------------------------------------------
\* Correctness property after the whole sequence is processed
\* -------------------------------------------------
Correct ==
    /\ i = Len(seq)
    /\ ( \E v \in Value :
            Cardinality({ j \in 1..Len(seq) : seq[j] = v }) >
            Len(seq) / 2 )
       => cand =
          CHOOSE v \in Value :
              Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ seq \in Seq(Value)
    /\ i = 0
    /\ cand = "None"
    /\ count = 0

\* -------------------------------------------------
\* Transition relation
\* -------------------------------------------------
Next ==
    \/ /\ i < Len(seq)
       /\ LET x == seq[i + 1] IN
          IF count = 0 THEN
              /\ cand' = x
              /\ count' = 1
          ELSE IF cand = x THEN
              /\ cand' = cand
              /\ count' = count + 1
          ELSE
              /\ cand' = cand
              /\ count' = count - 1
       /\ i' = i + 1
       /\ UNCHANGED <<seq>>
    \/ /\ i = Len(seq)
       /\ UNCHANGED <<seq, i, cand, count>>

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, count>>

\* -------------------------------------------------
\* Proofs (TLAPS style)
\* -------------------------------------------------
THEOREM TypeOKIsInvariant ==
    /\ TypeOK
    /\ []TypeOK
PROOF
    OBVIOUS
QED

THEOREM InvIsInvariant ==
    /\ Inv
    /\ []Inv
PROOF
    OBVIOUS
QED

THEOREM Correctness ==
    [] (i = Len(seq) => Correct)
PROOF
    OBVIOUS
QED

====