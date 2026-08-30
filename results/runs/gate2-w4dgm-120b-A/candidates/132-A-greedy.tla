---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in [1..bound -> Values]
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ cnt \in 0..bound

Init ==
    /\ seq \in [1..bound -> Values]
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

Scan ==
    /\ pos <= bound
    /\ LET x == seq[pos] IN
        /\ IF cnt = 0 THEN /\ cand' = x
                         /\ cnt' = 1
           ELSE IF x = cand THEN cnt' = cnt + 1
           ELSE cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Spec == Init /\ [][Scan]_vars

Correct ==
    /\ pos = bound + 1
    /\ \A x \in Values : (2 * Cardinality({i \in 1..bound : seq[i] = x}) > bound) => x = cand

Inv ==
    /\ pos \in 1..(bound + 1)
    /\ cnt \in 0..bound

BoundedSeq == [n \in 0..bound |-> [1..n -> Values]]

====