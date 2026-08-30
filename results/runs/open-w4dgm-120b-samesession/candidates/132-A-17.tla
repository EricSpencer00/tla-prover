---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in BoundedSeq(Values, bound)
    /\ pos \in Nat
    /\ cand \in Values \cup {"none"}
    /\ cnt \in Nat

\* BoundedSeq is a finite version of Sequence, built from the same primitives
\* so that the model stays within a checkable state space.
BoundedSeq(E, n) ==
    UNION { { f \in [1..k -> E] } : k \in 0..n }

Init ==
    /\ seq \in BoundedSeq(Values, bound)
    /\ pos = 1
    /\ cand \in Values \cup {"none"}
    /\ cnt = 0

\* The three-case update: candidate adoption, counter increment, or decrement.
Scan ==
    /\ pos <= Len(seq)
    /\ LET e == seq[pos] IN
        IF cand = "none" THEN
            /\ cand' = e
            /\ cnt' = 1
        ELSE IF cand = e THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
        ELSE
            /\ cand' = cand
            /\ cnt' = IF cnt > 0 THEN cnt - 1 ELSE 0
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Scan

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

\* Any element that truly is a majority of the scanned sequence must be the
\* surviving candidate once the scan has completed.
Correct ==
    \A e \in Values :
        (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq)
            => (cand = e \/ pos <= Len(seq)))

\* The counter always matches the strict-majority condition it records.
Inv ==
    \A e \in Values :
        cnt > 0 /\ cand # "none" => 2 * Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq)

Complete == pos > Len(seq)

\* Weak fairness on the scan: a non-empty finite sequence is always eventually
\* consumed, so the model never rests at an unfinished, deadlocked position.
Progress == \A e \in Values : Scan

====