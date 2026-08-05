---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Vals == {A, B, C}

VARIABLES seq, i, cand, cnt
vars == <<seq, i, cand, cnt>>

BoundedSeq == UNION {Seq(1..n, Vals) : n \in 0..bound}

TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Vals
    /\ cnt \in Nat

Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Vals
    /\ cnt = 0

Next ==
    \/ \E x \in Vals :
        /\ i <= Len(seq)
        /\ cand' = IF cnt = 0 THEN seq[i] ELSE cand
        /\ cnt' = IF cnt = 0 THEN 1
                 ELSE IF cand = seq[i] THEN cnt + 1
                 ELSE cnt - 1
        /\ i' = i + 1
    /\ UNCHANGED seq

Inv ==
    \A a \in Vals :
        (Cardinality({j \in 1..Len(seq) : seq[j] = a}) * 2 > Len(seq)) => (i > Len(seq) /\ cand = a)

Correct ==
    (i > Len(seq) /\ cnt > 0) => (\A a \in Vals : (Cardinality({j \in 1..Len(seq) : seq[j] = a}) * 2 > Len(seq)) => cand = a)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====