---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK == /\ Value \in FiniteSet
          /\ \A i \in 1..Len(seq) : seq[i] \in Value

\* ----------------------------------------------------------------------
\* State variables (inherited from the main specification)
\* ----------------------------------------------------------------------
VARIABLES seq, i, candidate, count, occ

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Positions before index i (1..i-1)
Before(i) == 1 .. (i - 1)

\* Occurrence count of a value up to position i (exclusive)
OccBefore(v, i) == Cardinality({ j \in Before(i) : seq[j] = v })

\* ----------------------------------------------------------------------
\* Initial state (inherited)
\* ----------------------------------------------------------------------
Init ==
    /\ i = 1
    /\ count = 0
    /\ candidate = CHOOSE v \in Value : TRUE \* arbitrary element
    /\ occ = [v \in Value |-> 0]

\* ----------------------------------------------------------------------
\* Transition (inherited)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ i <= Len(seq)
       /\ IF count = 0
          THEN /\ candidate' = seq[i]
               /\ count'     = 1
          ELSE IF seq[i] = candidate
               THEN /\ count' = count + 1
               ELSE /\ count' = count - 1
                     /\ candidate' = candidate
       /\ occ' = [occ EXCEPT ![candidate] = @ + IF seq[i] = candidate THEN 1 ELSE 0]
       /\ i'   = i + 1
       /\ UNCHANGED <<seq>>
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, candidate, count, occ>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, candidate, count, occ>>

\* ----------------------------------------------------------------------
\* Split invariant (inherited)
\* ----------------------------------------------------------------------
Inv ==
    /\ i \in 1 .. (Len(seq) + 1)
    /\ IF i <= Len(seq)
          THEN /\ candidate \in Value
               /\ count \in Nat
               /\ occ \in [Value -> Nat]
          ELSE /\ TRUE

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ i \in 1 .. (Len(seq) + 1)
    /\ candidate \in Value
    /\ count \in Nat
    /\ occ \in [Value -> Nat]
    /\ \A v \in Value : occ[v] = OccBefore(v, i)

\* ----------------------------------------------------------------------
\* Main correctness invariant
\* ----------------------------------------------------------------------
Correct ==
    /\ i > Len(seq)                     \* scanning complete
    /\ \A v \in Value :
          (2 * occ[v] > Len(seq)) => v = candidate

\* ----------------------------------------------------------------------
\* Theorem (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

\* ----------------------------------------------------------------------
\* Theorem (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []Correct

====