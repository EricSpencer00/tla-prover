---- MODULE MCMajority -------------------------------------------------
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

\* The original specification mistakenly asserted that `bound` is *not* a natural
\* number, which caused TLC to abort because the assumption was false.
\* Since `bound` is intended to be the maximum length of the sequences that
\* the algorithm processes, it must be a natural number (including zero).
\* We therefore replace the faulty assumption with a correct one that states
\* `bound` belongs to Nat.  This change is minimal and preserves the intended
\* semantics of the module.
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Majority vote algorithm (Boyer-Moore) for sequences over the set Value.
\* The algorithm works as follows:
\*   - i   : index of the next element to examine (1..Len(seq)+1)
\*   - cand: current candidate for the majority element
\*   - cnt : counter associated with the candidate
\* The algorithm is defined by the Init predicate and a Next relation.
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i = 1
    /\ cnt = 0
    /\ cand = CHOOSE x \in Value : TRUE  \* any value, irrelevant while cnt=0

Next ==
    \/ /\ i <= Len(seq)
       /\ IF cnt = 0 THEN
             /\ cand' = seq[i]
             /\ cnt'  = 1
          ELSE IF seq[i] = cand THEN
             /\ cand' = cand
             /\ cnt'  = cnt + 1
          ELSE
             /\ cand' = cand
             /\ cnt'  = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED <<seq>>
    \/ /\ i > Len(seq)          \* after the scan we may stay idle
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* The specification’s overall behavior
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Safety claim: the candidate after the scan is a majority element,
\* provided a majority element exists in the original sequence.
MajorityExists == 
    \E m \in Value :
        (Cardinality({j \in 1..Len(seq) : seq[j] = m}) > Len(seq) / 2)

\* Invariant expressing that when the scan is finished (i = Len(seq)+1) and a
\* majority element exists, the stored candidate must be that element.
MajorityInvariant ==
    (i = Len(seq) + 1) => (MajorityExists => cand \in { m \in Value :
        Cardinality({j \in 1..Len(seq) : seq[j] = m}) > Len(seq) / 2 })

=============================================================================