---- MODULE MCMajority ----
EXTENDS Integers, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

Seqs == UNION { [1..n -> Values] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

Init ==
    /\ seq \in Seqs
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

Next ==
    /\ \E e \in Values :
         /\ \E np \in 1..(IF Len(seq) = 0 THEN 1 ELSE Len(seq)) :
             /\ pos' = np
             /\ seq' = [1..np |-> e]
             /\ IF cnt = 0 THEN cand' = e ELSE cand' = cand
             /\ IF cnt = 0 \/ e = cand THEN cnt' = cnt + 1 ELSE cnt' = cnt - 1

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ seq \in Seqs
    /\ pos \in 1..(IF Len(seq) = 0 THEN 1 ELSE Len(seq))
    /\ cand \in Values
    /\ cnt \in 0..bound

Correct ==
    \A e \in Values :
        (cnt > 0 /\ \A i \in 1..Len(seq) : seq[i] = e) => cand = e

Inv ==
    \A e \in Values :
        (cnt > 0 /\ \A i \in 1..Len(seq) : seq[i] = e) => cand = e

SpecTypeOK == Spec /\ TypeOK
====