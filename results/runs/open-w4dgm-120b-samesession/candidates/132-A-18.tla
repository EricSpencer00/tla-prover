---- MODULE MCMajority ----
EXTENDS Sequences, FiniteSets

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq(S, n) == { f \in [1..n -> S] }

TypeOK ==
  /\ seq \in BoundedSeq(Values, bound)
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq(Values, bound)
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
  /\ UNCHANGED seq

Spec == Init /\ [][Step]_vars
  /\ WF_vars(Step) /\ WF_vars(\E x \in Values : Step)

Correct ==
  /\ pos = Len(seq) + 1
  /\ (\A y \in Values : Cardinality({i \in 1..Len(seq) : seq[i] = y}) * 2 > Len(seq) => y = cand)

Inv == \A i, j \in 1..Len(seq) : seq[i] = seq[j]

====