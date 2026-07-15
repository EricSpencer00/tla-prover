---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound
CONSTANT Seq = { f \in [1..n -> {A, B, C}] : n \in 0..bound }

VARIABLES inputSeq, Pos, Cand, Cnt

Init ==
    \E s \in Seq :
        /\ inputSeq = s
        /\ Pos = 1
        /\ Cand \in {A, B, C}
        /\ Cnt = 0

Scan ==
    /\ Pos <= Len(inputSeq)
    /\ LET e == inputSeq[Pos] IN
        /\ IF e = Cand THEN
                /\ Cand' = Cand
                /\ Cnt' = Cnt + 1
           ELSEIF Cnt = 0 THEN
                /\ Cand' = e
                /\ Cnt' = 1
           ELSE
                /\ Cand' = Cand
                /\ Cnt' = Cnt - 1
    /\ Pos' = Pos + 1

Done ==
    /\ Pos > Len(inputSeq)
    /\ UNCHANGED << inputSeq, Pos, Cand, Cnt >>

Next == Scan \/ Done

Spec == Init /\ [][Next]_<<inputSeq, Pos, Cand, Cnt>>

Count(e, s, m) == # { i \in 1..m : s[i] = e }

TypeOK ==
    /\ inputSeq \in Seq
    /\ Pos \in 1..(Len(inputSeq)+1)
    /\ Cand \in {A, B, C}
    /\ Cnt \in 0..Len(inputSeq)

Correct ==
    \A e \in {A, B, C} :
        (Count(e, inputSeq, Len(inputSeq)) > Len(inputSeq)/2) => Cand = e

Inv ==
    \A e \in {A, B, C} :
        Count(e, inputSeq, Pos-1) <= Count(Cand, inputSeq, Pos-1)

====