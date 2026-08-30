---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, candidate, cnt

vars == <<seq, pos, candidate, cnt>>

BoundedSeq == { f \in [1..n -> Values] : n \in 0..bound }

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(bound + 1)
  /\ candidate \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ candidate \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       \/ (cnt = 0) /\ candidate' = x /\ cnt' = 1
       \/ (candidate = x) /\ cnt' = cnt + 1
       \/ (candidate # x) /\ cnt > 0 /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Scan]_vars

Correct ==
  /\ Len(seq) >= 1
  /\ \A x \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = x }) > Len(seq)) => (x = candidate)

Inv ==
  /\ pos >= 1
  /\ pos <= Len(seq) + 1
  /\ cnt >= 0
  /\ cnt <= Len(seq)

Next == Scan

StateConstraint == TypeOK /\ Inv

====