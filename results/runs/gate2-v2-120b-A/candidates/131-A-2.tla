---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

\* ------------------------------------------------------------
\* Constants
\* ------------------------------------------------------------
CONSTANT Value

\* ------------------------------------------------------------
\* State variables (inherited from the main algorithm)
\* ------------------------------------------------------------
VARIABLES candidate, count, i, seq

\* ------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------
\* The domain of indices for the sequence (1..Len)
Indices == 1 .. Len

\* Length of the input sequence
Len == Len(seq)

\* Predicate stating that i points to the next element to process
\* (i ranges from 1 to Len+1, where Len+1 means all elements processed)
NextToProcess == i \in 1 .. (Len + 1)

\* ------------------------------------------------------------
\* Initial state (inherits the algorithm's Init)
\* ------------------------------------------------------------
Init ==
    /\ i = 1
    /\ count = 0
    /\ candidate \in Value
    /\ seq \in [Indices -> Value]

\* ------------------------------------------------------------
\* Transition relation (inherits the algorithm's Next)
\* ------------------------------------------------------------
Next ==
    \/ /\ i <= Len
       /\ LET x == seq[i] IN
          IF count = 0 THEN
              /\ candidate' = x
              /\ count' = 1
          ELSE IF x = candidate THEN
              /\ count' = count + 1
              /\ candidate' = candidate
          ELSE
              /\ count' = count - 1
              /\ candidate' = candidate
       /\ i' = i + 1
    \/ /\ i = Len + 1
       /\ UNCHANGED <<candidate, count, seq, i>>

\* ------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------
Spec == Init /\ [][Next]_<<candidate, count, seq, i>>

\* ------------------------------------------------------------
\* Type correctness invariant (all variables stay within their domains)
\* ------------------------------------------------------------
TypeOK ==
    /\ i \in 1 .. (Len + 1)
    /\ count \in Nat
    /\ candidate \in Value
    /\ seq \in [Indices -> Value]

\* ------------------------------------------------------------
\* Main correctness invariant (Inv) – the candidate, if a strict majority
\* element exists in the whole sequence, must equal that element.
\* ------------------------------------------------------------
\* The number of occurrences of a value v in the whole sequence:
Occurences(v) == Cardinality({j \in Indices : seq[j] = v})

\* The set of values that appear in a strict majority (> Len/2 times):
MajorityValues == {v \in Value : Occurences(v) > Len / 2}

Inv ==
    MajorityValues = {} \/ candidate \in MajorityValues

\* ------------------------------------------------------------
\* Derived invariant alias expected by the .cfg
\* ------------------------------------------------------------
Correct == Inv

\* ------------------------------------------------------------
\* THEOREM (optional, for TLAPS) that the invariants hold under Spec
\* ------------------------------------------------------------
THEOREM SpecImpliesInv ==
    Spec => []Inv

=============================================================================