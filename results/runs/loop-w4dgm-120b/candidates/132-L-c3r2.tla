---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS A, B, C, bound

\* BoundedSeq is defined here as a finite version of Seq so the model is
\* checkable; it replaces the standard Seq operator from Sequences.
BoundedSeq(f) == IF f = <<>> THEN f ELSE Head(f) \o BoundedSeq(Tail(f))

VARIABLES seq, pos, cand, count
vars == <<seq, pos, cand, count>>

\* The state space is sequences of length up to bound over the three values.
Sequences == {BoundedSeq(f) : f \in [1..bound -> {A, B, C}]}

TypeOK ==
    /\ seq \in Sequences
    /\ pos \in 1..(bound + 1)
    /\ cand \in {A, B, C}
    /\ count \in 0..bound

Init ==
    /\ seq \in Sequences
    /\ pos = 1
    /\ cand \in {A, B, C}
    /\ count = 0

\* Boyer-Moore scan: the three cases of the majority test.
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
        /\ IF pos = 1 THEN cand' = x ELSE
            IF x = cand THEN cand' = cand ELSE IF count = 0 THEN cand' = x ELSE cand'
        /\ count' = IF x = cand THEN count + 1 ELSE IF count = 0 THEN 1 ELSE count - 1
    /\ pos' = pos + 1

Complete ==
    /\ pos > Len(seq)
    /\ UNCHANGED vars

Next == Scan \/ Complete

Spec == Init /\ [][Next]_vars /\ SF_vars(Scan)

\* Any element that truly holds a majority must equal the final candidate.
Correct == \A x \in {A, B, C} : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => x = cand

\* The reduced counter is always a strict majority of the scanned prefix.
Inv == count > Len(seq) \div 2

Liveness == WF_vars(Complete)

====