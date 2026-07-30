---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq == UNION { [1 .. n -> Values] : n \in 0 .. bound }

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in 1 .. (bound + 1)
    /\ cand \in Values
    /\ cnt \in 0 .. bound

Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

Bump(n) == IF n < bound + 1 THEN n + 1 ELSE n

Next ==
    \/ \E x \in Values :
        /\ pos <= bound
        /\ seq' = [seq EXCEPT ![pos] = x]
        /\ pos' = Bump(pos)
        /\ IF cnt = 0 THEN cand' = x /\ cnt' = 1
           ELSE IF x = cand THEN cnt' = cnt + 1 /\ cand' = cand
           ELSE cnt' = cnt - 1 /\ cand' = cand
    \/ \E n \in 0 .. bound :
        /\ seq' = [k \in 1 .. n |-> seq[k]]
        /\ pos' = 1
        /\ cand' = cand
        /\ cnt' = cnt

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

Counts(e) == Cardinality({k \in 1 .. Len(seq) : seq[k] = e})

Correct ==
    \A e \in Values : (Counts(e) * 2 > Len(seq)) => (e = cand)

Inv == TypeOK

====