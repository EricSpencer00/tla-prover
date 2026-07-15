---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Seq \in Seq(Value)
    /\ Candidate \in Value
    /\ Count \in Nat

\* ----------------------------------------------------------------------
\* Helper definitions (imported from the main specification)
\* ----------------------------------------------------------------------
Seq == <<>>          \* placeholder: the actual sequence is a constant
Candidate == CHOOSE v \in Value : TRUE \* placeholder
Count == 0          \* placeholder

\* ----------------------------------------------------------------------
\* State variables (no new variables are introduced)
\* ----------------------------------------------------------------------
VARIABLES Candidate, Count

\* ----------------------------------------------------------------------
\* Initial state (inherited from the main specification)
\* ----------------------------------------------------------------------
Init ==
    /\ Candidate \in Value
    /\ Count = 0

\* ----------------------------------------------------------------------
\* Next-state relation (inherited, represented as a stub)
\* ----------------------------------------------------------------------
Next ==
    /\ \E i \in 1..Len(Seq) :
         /\ IF i = Len(Seq) THEN
                UNCHANGED << Candidate, Count >>
            ELSE
                IF Seq[i] = Candidate THEN
                    Candidate' = Candidate /\ Count' = Count + 1
                ELSE IF Count = 0 THEN
                    Candidate' = Seq[i] /\ Count' = 1
                ELSE
                    Candidate' = Candidate /\ Count' = Count - 1

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Candidate, Count>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv == 
    /\ TypeOK
    /\ (Count = 0) => TRUE   \* placeholder for the true invariant

\* ----------------------------------------------------------------------
\* Main correctness invariant (placeholder, to be proved by TLAPS)
\* ----------------------------------------------------------------------
Correct == 
    /\ (Count > 0) => (Candidate = (CHOOSE v \in Value : 
          Cardinality({ i \in 1..Len(Seq) : Seq[i] = v }) > Len(Seq) / 2))

\* ----------------------------------------------------------------------
\* Theorems (TLAPS proofs would be attached to these)
\* ----------------------------------------------------------------------
THEOREM TypeOKInv == Spec => []TypeOK
THEOREM InvInv == Spec => []Inv
THEOREM CorrectInv == Spec => []Correct

====