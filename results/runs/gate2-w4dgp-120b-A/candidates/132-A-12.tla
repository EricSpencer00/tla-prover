---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

BoundedSeq(T) == UNION { [1 .. n -> T] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ pos \in 1 .. (bound + 1)
    /\ cand \in Values
    /\ cnt \in 0 .. bound

Init ==
    /\ seq \in BoundedSeq(Values)
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
         /\ IF cnt = 0
              THEN cand' = x /\ cnt' = 1
              ELSE IF x = cand
                     THEN cnt' = cnt + 1
                     ELSE cnt' = cnt - 1
         /\ UNCHANGED <<seq, pos>>
    /\ pos' = pos + 1

Spec == Init /\ [][Scan]_vars

Correct ==
    \A v \in Values :
        (2 * (Cardinality {i \in 1 .. Len(seq) : seq[i] = v}) > Len(seq))
            => v = cand

Inv ==
    cnt = 0 => cand = seq[1]

Eventual ==
    WF_vars(Scan)

====