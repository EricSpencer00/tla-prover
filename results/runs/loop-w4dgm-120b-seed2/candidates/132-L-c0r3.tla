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
        IF cnt = 0 THEN /\ cand' = x
                       /\ cnt' = 1
        ELSE IF x = cand THEN /\ cnt' = cnt + 1
                             /\ UNCHANGED cand
        ELSE /\ cnt' = cnt - 1
             /\ UNCHANGED cand
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Scan

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

Correct ==
    \A e \in Values :
        (\A i \in 1..bound : seq[i] = e) => (cand = e)

Inv ==
    /\ cnt >= 0
    /\ (cnt = 0 => TRUE)
    /\ (cnt > 0 => cand \in Values)

BoundedSeq == [1..bound -> Values]

====