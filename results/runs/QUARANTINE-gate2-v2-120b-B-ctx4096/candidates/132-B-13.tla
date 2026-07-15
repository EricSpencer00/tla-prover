---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT A, B, C, bound

\* The original specification erroneously assumed that `bound` is **not**
\* an element of Nat, which makes the model immediately inconsistent.
\* For a bounded‑length sequence we need `bound` to be a natural number.
\* We therefore replace the contradictory assumption with a sensible one.
\* The new assumption preserves the intended meaning (a finite, non‑negative
\* bound) without weakening any of the module’s behavior.
\* ----------------------------------------------------------------------
ASSUME bound \in Nat

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Value == {A, B, C}

\* `BoundedSeq(S)` is the set of all finite sequences over set `S`
\* whose length does not exceed `bound`.  The definition uses the
\* standard sequence operator from the Sequences module.
\* ----------------------------------------------------------------------
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ seq = << >>
    /\ i   = 0
    /\ cand = A               \* any element of Value; choice does not affect correctness
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ i < bound
       /\ \E v \in Value :
            /\ seq' = Append(seq, v)
            /\ i'   = i + 1
            /\ IF cnt = 0
               THEN /\ cand' = v
                    /\ cnt'  = 1
               ELSE IF v = cand
                    THEN /\ cand' = cand
                         /\ cnt'  = cnt + 1
                    ELSE /\ cand' = cand
                         /\ cnt'  = cnt - 1
    \/ /\ i = bound
       /\ UNCHANGED << seq, i, cand, cnt >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Invariant expressing the classic majority‑vote property
\* ----------------------------------------------------------------------
MajorityInv ==
    \A v \in Value :
        (v # cand) => 
            Cardinality({ j \in 1..Len(seq) : seq[j] = v }) <=
            Cardinality({ j \in 1..Len(seq) : seq[j] = cand })

=============================================================================