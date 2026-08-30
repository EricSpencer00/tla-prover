---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Numbers == {A, B, C}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
    /\ seq \in Seq(Numbers)
    /\ pos \in 1..(Len(seq) + 1)
    /\ cand \in Numbers
    /\ count \in 0..bound

Init ==
    /\ seq \in { s \in Seq(Numbers) : Len(s) <= bound }
    /\ pos = 1
    /\ cand \in Numbers
    /\ count = 0

Poll ==
    /\ pos <= Len(seq)
    /\ \E x \in Numbers :
        \/ (x = seq[pos] /\ cand' = x /\ count' = IF x = cand THEN count + 1 ELSE 1)
        \/ (x # seq[pos] /\ x = cand /\ count > 0 /\ count' = count - 1)
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq>>

Done ==
    /\ pos > Len(seq)
    /\ UNCHANGED vars

Next == Poll \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Poll)

Correct ==
    /\ (pos = Len(seq) + 1 <=> \A x \in Numbers : 2 * Cardinality({ i \in 1..Len(seq) : seq[i] = x }) > Len(seq))
    /\ (pos = Len(seq) + 1 /\ count > 0 => cand = seq[pos - 1])

Inv ==
    /\ (pos = Len(seq) + 1 <=> \A x \in Numbers : 2 * Cardinality({ i \in 1..Len(seq) : seq[i] = x }) > Len(seq))
    /\ (pos = Len(seq) + 1 /\ count > 0 => cand = seq[pos - 1])

BoundedSeq == Seq

====