---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

Seqs == UNION { [2 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1 .. (IF seq = << >> THEN 1 ELSE Len(seq) + 1)
  /\ cand \in Values
  /\ cnt \in 0 .. bound

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x
                      /\ cnt' = 1
       ELSE IF cand = x THEN /\ cnt' = cnt + 1
       ELSE /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Scan]_vars

Correct ==
  /\ (cnt > 0 => cand = A)
  /\ (cnt > 1 => cand = B)

Inv ==
  /\ cnt >= 0
  /\ cnt <= bound
  /\ IF pos <= Len(seq) THEN cand \in Values ELSE TRUE

Completed == <>(pos > Len(seq))

====