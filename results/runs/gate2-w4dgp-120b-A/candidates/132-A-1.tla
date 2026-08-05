---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Vals == {A, B, C}

VARIABLES seq, pos, cand, cnt
vars == <<seq, pos, cand, cnt>>

BoundedSeq == { s \in Seq(Vals) : Len(s) <= bound }

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Vals
  /\ cnt = 0

Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x /\ cnt' = 1
       ELSE IF x = cand THEN cnt' = cnt + 1 /\ UNCHANGED cand
       ELSE cnt' = cnt - 1 /\ UNCHANGED cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Step]_vars /\ WF_vars(Step)

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in Nat
  /\ cand \in Vals
  /\ cnt \in Nat

Correct ==
  (pos > Len(seq) /\ cnt > 0 /\ cnt * 2 > Len(seq)) => (cand \in Vals /\ cnt > 0)

Inv ==
  (pos > Len(seq) /\ cnt > 0 /\ cnt * 2 > Len(seq)) => (cand \in seq)

Complete == (pos > Len(seq)) ~> FALSE

====