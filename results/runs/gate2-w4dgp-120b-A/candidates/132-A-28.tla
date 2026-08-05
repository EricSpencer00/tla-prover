---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Q == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq(S, n) == UNION { [1..m -> S] : m \in 0..n }

TypeOK ==
    /\ seq \in BoundedSeq(Q, bound)
    /\ pos \in Nat
    /\ cand \in Q
    /\ cnt \in Nat

Init ==
    /\ seq \in BoundedSeq(Q, bound)
    /\ pos = 1
    /\ cand \in Q
    /\ cnt = 0

Next(c) ==
    /\ c \in Q
    /\ pos <= Len(seq)
    /\ IF cnt = 0
       THEN /\ cand' = c
            /\ cnt' = 1
       ELSE IF cand = c
            THEN cnt' = cnt + 1
            ELSE cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

NextS == \E c \in Q : Next(c)

Spec ==
    /\ Init
    /\ [][NextS]_vars
    /\ WF_vars(NextS)

Correct ==
    \A x \in Q : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => cand = x

Inv ==
    cnt <= Len(seq)

AllScanned == (pos > Len(seq)) ~> (pos > Len(seq))

====