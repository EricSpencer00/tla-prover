---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

VARIABLES seq, pos, cand, cnt

TypeOK ==
  /\ seq \in Seq
  /\ pos \in 0..5
  /\ cand \in {A, B, C}
  /\ cnt \in 0..5

Init ==
  /\ seq \in Seq
  /\ pos = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

Next ==
  /\ \/ /\ pos < Len(seq)
        /\ LET x == seq[pos + 1] IN
             IF cnt = 0 THEN /\ cand' = x /\ cnt' = 1
             ELSE IF cand = x THEN cnt' = cnt + 1 /\ cand' = cand
             ELSE cnt' = cnt - 1 /\ cand' = cand
        /\ pos' = pos + 1
        /\ seq' = seq
     \/ /\ pos = Len(seq)
        /\ \E s \in Seq :
              /\ seq' = s
              /\ pos' = 1
              /\ cand' = cand
              /\ cnt' = cnt
        /\ UNCHANGED <<cand, cnt>>
  /\ UNCHANGED <<cand, cnt>>

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

Correct ==
  \A x \in {A, B, C} :
    (cnt > 0 /\ pos > Len(seq) /\ \E i \in 1..Len(seq) : seq[i] = x) => cand = x

Inv ==
  \A x \in {A, B, C} :
    ((cnt > 0 /\ pos > Len(seq) /\ \E i \in 1..Len(seq) : seq[i] = x)
       => \E i \in 1..Len(seq) : seq[i] = x)

Complete == pos = Len(seq) + 1

Properties == {Complete}

====