---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

VALUES == {A, B, C}

VARIABLES s, pos, cand, cnt

TypeOK ==
    /\ s \in Seq
    /\ s \in [1..bound -> VALUES]
    /\ pos \in 0..bound
    /\ cand \in VALUES \cup {"none"}
    /\ cnt \in 0..bound

Init ==
    /\ s \in Seq
    /\ pos = 1
    /\ cand \in VALUES \cup {"none"}
    /\ cnt = 0

Next ==
    \/ \E v \in VALUES :
         /\ pos <= bound
         /\ IF cand = "none" THEN
              /\ cand' = v
              /\ cnt' = 1
            ELSE IF cand = v THEN
              /\ cnt' = cnt + 1
              /\ cand' = cand
            ELSE IF cnt > 0 THEN
              /\ cnt' = cnt - 1
              /\ cand' = cand
            ELSE
              /\ cnt' = 0
              /\ cand' = v
         /\ pos' = IF pos < bound THEN pos + 1 ELSE bound
         /\ UNCHANGED s
    \/ \E w \in Seq :
         /\ w \in [1..bound -> VALUES]
         /\ s' = w
         /\ pos' = 1
         /\ cand' \in VALUES \cup {"none"}
         /\ cnt' = 0

Spec == Init /\ [][Next]_<<s, pos, cand, cnt>>

Correct ==
    (cnt > 0 /\ pos > bound) => (\A j \in 1..bound : s[j] = cand)

Inv == TRUE

====