---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

BoundedSeq(Vals, k) == {f \in [1..n -> Vals] : n \in 0..k}

Init ==
    /\ seq \in BoundedSeq(Values, bound)
    /\ pos \in 1..(Len(seq) + 1)
    /\ cand \in Values
    /\ count \in 0..bound

Step ==
    \/ pos <= Len(seq) /\ LET e == seq[pos] IN
        /\ IF count = 0 THEN cand' = e /\ count' = 1
           ELSE IF e = cand THEN count' = count + 1
           ELSE count' = count - 1
        /\ pos' = pos + 1
        /\ UNCHANGED seq
    \/ \E e \in Values:
        /\ seq' = Append(seq, e)
        /\ UNCHANGED <<pos, cand, count>>

Spec == Init /\ [][Step]_vars
    WF_vars(Step)

TypeOK ==
    /\ seq \in BoundedSeq(Values, bound)
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ count \in 0..bound

Correct ==
    (pos > Len(seq) /\ count > 0) => (2 * count > Len(seq) => cand = Values)

Inv ==
    /\ pos \in 1..(bound + 1)
    /\ count \in 0..bound
    /\ seq \in BoundedSeq(Values, bound)

====