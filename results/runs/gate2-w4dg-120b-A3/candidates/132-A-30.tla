---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in (1..bound \rightarrow Values) \cup {<< >>}
  /\ pos \in 0..bound
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ \E n \in 0..bound : seq \in [1..n -> Values]
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x /\ cnt' = 1
                    ELSE IF x = cand THEN cnt' = cnt + 1 /\ cand' = cand
                    ELSE cnt' = cnt - 1 /\ cand' = cand
  /\ pos' = pos + 1

Next_ == Step

Spec == Init /\ [][Next_]_vars

Correct == (cnt = 0) => ((\E i \in 1..Len(seq) : seq[i] = cand) => (Pos(seq, cand) > Len(seq) / 2))

Inv == TypeOK /\ Correct

Completion == pos > Len(seq)

====