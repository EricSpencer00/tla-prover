---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq(S) == UNION { { f \in [1..n -> S] } : n \in 0..bound }

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x /\ cnt' = 1
       ELSE IF x = cand THEN cnt' = cnt + 1 /\ cand' = cand
       ELSE cnt' = cnt - 1 /\ cand' = cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Scan]_vars
  /\ WF_vars(Scan)

Correct ==
  \A e \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq)) => (cand = e)

Inv ==
  \A e \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq)) => (cand = e)

Properties == Spec /\ Correct /\ Inv

====