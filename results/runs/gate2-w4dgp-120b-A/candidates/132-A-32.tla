---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

Vals == {A, B, C}
Seqs == UNION { [1..n -> Vals] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

TypeOK ==
    /\ seq \in Seqs
    /\ i \in 0..bound
    /\ cand \in Vals
    /\ cnt \in 0..bound

Init ==
    /\ seq \in Seqs
    /\ i = 1
    /\ cand \in Vals
    /\ cnt = 0

ScanNext ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
        /\ IF cnt = 0
           THEN /\ cand' = x
                /\ cnt' = 1
           ELSE IF x = cand
                THEN cnt' = cnt + 1
                ELSE cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

Done ==
    /\ i > Len(seq)
    /\ UNCHANGED vars

Next == ScanNext \/ Done

Spec == Init /\ [][Next]_vars
    /\ WF_vars(ScanNext)

Correct ==
    (i > Len(seq) /\ cnt > 0) => (\A j \in 1..Len(seq) : seq[j] = cand)

Inv ==
    cnt >= 0

BoundedSeq == Seq

====