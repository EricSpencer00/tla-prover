---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Set of possible element values
Values == { A, B, C }

\* Bounded sequences of length at most **bound**
BoundedSeq(N) == { s \in Seq : Len(s) <= N }

VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(bound)
    /\ i \in Nat
    /\ cnt \in Nat
    /\ cand \in Values

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(bound)
    /\ i = 1
    /\ cnt = 0
    /\ cand \in Values

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ProcessedIndices ==
    IF i > 1 THEN 1..(i - 1) ELSE {}

Count(v) ==
    Cardinality({ j \in ProcessedIndices : seq[j] = v })

\* ----------------------------------------------------------------------
\* Invariant used in proofs
\* ----------------------------------------------------------------------
Inv ==
    /\ cnt = 2 * Count(cand) - (i - 1)
    /\ cnt >= 0

\* ----------------------------------------------------------------------
\* Majority predicate and safety property
\* ----------------------------------------------------------------------
Majority(v) ==
    Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2

Correct ==
    (i > Len(seq) /\ \E v \in Values : Majority(v))
        => \E v \in Values : Majority(v) /\ cand = v

\* ----------------------------------------------------------------------
\* Main algorithm step (scan next element)
\* ----------------------------------------------------------------------
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
       IF cnt = 0 THEN
           /\ cand' = x
           /\ cnt' = 1
       ELSE IF cand = x THEN
           /\ cand' = cand
           /\ cnt' = cnt + 1
       ELSE
           /\ cand' = cand
           /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* Next-state relation (including stuttering after the scan finishes)
\* ----------------------------------------------------------------------
Next ==
    Scan
    \/ (i > Len(seq) /\ UNCHANGED << seq, i, cand, cnt >>)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< seq, i, cand, cnt >>

=============================================================================