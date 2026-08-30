---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in [1..bound -> Values]
  /\ pos \in 0..bound
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in [1..bound -> Values]
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= bound
  /\ LET a == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = a
                      /\ cnt' = 1
       ELSE IF a = cand THEN /\ cand' = cand
                           /\ cnt' = cnt + 1
       ELSE /\ cand' = cand
            /\ cnt' = cnt - 1
  /\ pos' = pos + 1

Next == Scan

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

Correct ==
  \A e \in Values : (Cardinality({i \in 1..bound : seq[i] = e}) * 2 > bound) => e = cand

Inv == cnt <= 2 * Cardinality({i \in 1..bound : seq[i] = cand})

Completion == WF_vars(Scan)

BoundedSeq ==
  Len(\E s \in [1..bound -> Values] : s = seq) = bound
====