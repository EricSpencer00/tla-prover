---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* --------------------------------------------------------------
\* Value set of the three distinct elements
\* --------------------------------------------------------------
ValueSet == { A, B, C }

\* --------------------------------------------------------------
\* BoundedSeq: finite sequences over a set, limited by the constant bound
\* --------------------------------------------------------------
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* --------------------------------------------------------------
\* State variables
\* --------------------------------------------------------------
VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------
Count(s, v) == Cardinality({ j \in 1..Len(s) : s[j] = v })

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* --------------------------------------------------------------
\* Transition relation
\* --------------------------------------------------------------
ScanStep ==
    LET x == seq[i] IN
    IF cnt = 0 THEN
        /\ cand' = x
        /\ cnt'  = 1
    ELSE IF cand = x THEN
        /\ cand' = cand
        /\ cnt'  = cnt + 1
    ELSE
        /\ cand' = cand
        /\ cnt'  = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

Next ==
    \/ /\ i <= Len(seq)
       /\ ScanStep
    \/ /\ i > Len(seq)
       /\ UNCHANGED << seq, i, cand, cnt >>

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* --------------------------------------------------------------
\* Invariants
\* --------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i \in Nat
    /\ 1 <= i <= Len(seq) + 1
    /\ cand \in ValueSet
    /\ cnt \in Nat

Correct ==
    (i = Len(seq) + 1) =>
        \A v \in ValueSet :
            (Count(seq, v) > Len(seq) / 2) => cand = v

Inv ==
    /\ cnt >= 0
    /\ cnt =
        Cardinality({ j \in 1..Len(seq) : j < i /\ seq[j] = cand })
        -
        Cardinality({ j \in 1..Len(seq) : j < i /\ seq[j] # cand })

====