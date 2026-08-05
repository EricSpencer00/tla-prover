---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Vals == {A, B, C}
M == 2

VARIABLES seq, k, cand, cnt

vars == <<seq, k, cand, cnt>>

RECURSIVE BoundedSeq(_)
BoundedSeq(n) == IF n = 0 THEN {<< >>}
                 ELSE LET p == BoundedSeq(n - 1) IN {s \o <<x>> : s \in p, x \in Vals}

Seqs == UNION {BoundedSeq(n) : n \in 0..bound}

Init ==
    /\ seq \in Seqs
    /\ k = 1
    /\ cand \in Vals
    /\ cnt = 0

Step(x) ==
    /\ k <= Len(seq)
    /\ IF cnt = 0 THEN cand' = x /\ cnt' = 1
       ELSE IF cand = x THEN cnt' = cnt + 1 /\ cand' = cand
       ELSE cnt' = cnt - 1 /\ cand' = cand
    /\ k' = k + 1
    /\ UNCHANGED seq

Next ==
    \/ \E x \in Vals : Step(x)
    \/ /\ k > Len(seq) /\ UNCHANGED vars
    \/ \E s \in Seqs : s # seq /\ seq' = s /\ k' = 1 /\ UNCHANGED <<cand, cnt>>

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E x \in Vals : Step(x))

TypeOK ==
    /\ seq \in Seqs
    /\ k \in Nat
    /\ cand \in Vals
    /\ cnt \in 0..M

Correct ==
    \A x \in Vals :
        (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => cand = x

Inv ==
    (cnt = 0) => (k = 1 \/ k = Len(seq) + 1)

Prop ==
    (k > Len(seq)) ~> (k > Len(seq))

====