---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}
Seqs == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in Seqs
    /\ pos \in 1 .. (IF seq = [1 .. 0 -> Values] THEN 1 ELSE Len(seq) + 1)
    /\ cand \in Values
    /\ cnt \in 0 .. bound

Init ==
    /\ seq \in Seqs
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

Scan ==
    /\ pos <= Len(seq)
    /\ IF cnt = 0 THEN
         /\ cand' = seq[pos]
         /\ cnt' = 1
       ELSE IF seq[pos] = cand THEN
         /\ cnt' = cnt + 1
         /\ UNCHANGED cand
       ELSE
         /\ cnt' = cnt - 1
         /\ UNCHANGED cand
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Scan

Spec == Init /\ [][Next]_vars

Correct ==
    (cnt > 0 /\ pos > Len(seq)) =>
        \A i \in 1 .. Len(seq) : seq[i] = cand

Inv == TypeOK /\ Correct

====