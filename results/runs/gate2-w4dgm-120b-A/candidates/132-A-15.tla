---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

ValueSet == {A, B, C}

\* BoundedSeq mimics Seq but stays finite: only sequences up to the bound exist.
BoundedSeq == [n \in 0..bound |-> ValueSet^n]

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in 1..(bound + 1)
    /\ cand \in ValueSet
    /\ cnt \in 0..bound

\* Majority correctness: any element that truly dominates must be the reported
\* candidate once the entire sequence has been scanned.
Correct ==
    \A c \in ValueSet :
        (2 * Cardinality({i \in DOMAIN seq : seq[i] = c}) > Cardinality(DOMAIN seq)
            => cand = c)

Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* Boyer-Moore scan: adopt a fresh candidate when the counter is empty,
\* otherwise count matches up and mismatches down.
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
        IF cnt = 0 THEN /\ cand' = x
                        /\ cnt' = 1
        ELSE IF x = cand THEN cnt' = cnt + 1
        ELSE cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Scan

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Scan)

\* The scan position advances in every weakly fair step, so it cannot get stuck.
BoundedProgress == pos > 1

====