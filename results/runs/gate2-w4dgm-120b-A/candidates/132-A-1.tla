---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in BoundedSeq(Values, bound)
    /\ pos \in 0..bound
    /\ cand \in Values
    /\ cnt \in 0..bound

Init ==
    /\ seq \in BoundedSeq(Values, bound)
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

Step ==
    /\ pos <= Len(seq)
    /\ LET cur == seq[pos] IN
        IF cnt = 0 THEN cand' = cur /\ cnt' = 1
        ELSE IF cur = cand THEN cnt' = cnt + 1 /\ cand' = cand
        ELSE cnt' = cnt - 1 /\ cand' = cand
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Spec == Init /\ [][Step]_vars
    /\ WF_vars(Step)

Correct == (\E i \in 1..Len(seq) : (2 * Cardinality({j \in 1..Len(seq) : seq[j] = seq[i]}) > Len(seq))
    => seq[i] = cand)
Inv == (\A e \in Values : (2 * Cardinality({j \in 1..Len(seq) : seq[j] = e}) <= Len(seq)) \/ e = cand)

BoundedSeq(Vals, n) ==
    UNION { [i \in 1..k -> Vals] : k \in 0..n }

====