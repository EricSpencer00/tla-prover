---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS A, B, C, bound, Seq

VARIABLES InputSeq, pos, candidate, counter

ElemSet == {A, B, C}

Count(e, seq) == 
    Len({i \in 1..Len(seq) : seq[i] = e})

Init ==
    /\ InputSeq \in Seq
    /\ pos = 1
    /\ candidate \in ElemSet
    /\ counter = 0

Scan ==
    /\ pos <= Len(InputSeq)
    /\ LET current == InputSeq[pos] IN
       /\ IF current = candidate THEN
            /\ counter' = counter + 1
            /\ pos' = pos + 1
            /\ UNCHANGED InputSeq
          ELSE IF current # candidate /\ counter > 0 THEN
            /\ counter' = counter - 1
            /\ pos' = pos + 1
            /\ UNCHANGED InputSeq
          ELSE
            /\ counter' = 1
            /\ candidate' = current
            /\ pos' = pos + 1
            /\ UNCHANGED InputSeq

Next == Scan

TypeOK ==
    /\ InputSeq \in Seq
    /\ pos \in 1..Len(InputSeq)+1
    /\ candidate \in ElemSet
    /\ counter \in 0..Len(InputSeq)

Correct ==
    /\ pos = Len(InputSeq) + 1
    /\ \E majority \in ElemSet :
         (Count(majority, InputSeq) > Len(InputSeq)/2) => candidate = majority

Inv ==
    /\ pos \in 1..Len(InputSeq)+1
    /\ \A e \in ElemSet : Count(candidate, InputSeq[1..pos-1]) >= Count(e, InputSeq[1..pos-1])

Spec == Init /\ [][Next]_<<InputSeq, pos, candidate, counter>>

====