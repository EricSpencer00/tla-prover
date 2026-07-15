---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound, Seq

VARIABLES seq, i, cand, cnt

ElemSet == {A, B, C}

TypeOK ==
    /\ seq \in [1..Len(seq) -> ElemSet]
    /\ i \in 1..Len(seq)+1
    /\ cand \in ElemSet
    /\ cnt \in Nat

Count(e) ==
    Len({ j \in 1..Len(seq) : seq[j] = e })

Correct ==
    IF \E e \in ElemSet : Count(e) > Len(seq)/2 THEN
        cand = e
    ELSE
        TRUE

Inv == TypeOK /\ Correct

Init ==
    /\ seq \in Seq
    /\ i = 1
    /\ cand \in ElemSet
    /\ cnt = 0

ScanSame ==
    /\ i <= Len(seq)
    /\ seq[i] = cand
    /\ cnt' = cnt + 1
    /\ i' = i + 1
    /\ UNCHANGED <<cand, seq>>

ScanAdopt ==
    /\ i <= Len(seq)
    /\ seq[i] # cand
    /\ cand' = seq[i]
    /\ cnt' = 0
    /\ i' = i + 1
    /\ UNCHANGED <<seq>>

ScanDec ==
    /\ i <= Len(seq)
    /\ seq[i] # cand
    /\ cnt > 0
    /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED <<cand, seq>>

ScanDone ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == ScanSame \/ ScanAdopt \/ ScanDec \/ ScanDone

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

====