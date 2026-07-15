---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound, Seq

VARIABLES seq, pos, cand, cnt

Vals == {A, B, C}

Count(s, e) == CARD({ i \in 1..Len(s) : s[i] = e })
Majority(s, e) == Count(s, e) > Len(s) / 2

TypeOK ==
    /\ seq \in Seq
    /\ pos \in 1..Len(seq)+1
    /\ cand \in Vals
    /\ cnt \in 0..Len(seq)

Init ==
    /\ seq \in Seq
    /\ pos = 1
    /\ cand \in Vals
    /\ cnt = 0

Scan ==
    /\ pos <= Len(seq)
    /\ LET e == seq[pos] IN
        IF e = cand THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
        ELSE IF cnt = 0 THEN
            /\ cand' = e
            /\ cnt' = 1
        ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1
        /\ pos' = pos + 1
        /\ UNCHANGED seq

Stutter ==
    /\ pos > Len(seq)
    /\ UNCHANGED <<seq, pos, cand, cnt>>

Next == Scan \/ Stutter

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

Correct ==
    IF pos > Len(seq) THEN
        \A e \in Vals: ~Majority(seq, e) \/ e = cand
    ELSE
        TRUE

Inv ==
    cnt = 2 * Count(seq[1..pos-1], cand) - (pos-1)

====