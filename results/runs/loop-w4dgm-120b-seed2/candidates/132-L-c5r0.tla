---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
Vars == {"seq", "pos", "candidate", "cnt"}

TypeOK ==
  /\ seq \in [1..bound -> Values]
  /\ pos \in 0..bound
  /\ candidate \in Values
  /\ cnt \in 0..bound

Init ==
  /\ \E n \in 0..bound, f \in [1..n -> Values] : seq = [i \in 1..bound |-> IF i <= n THEN f[i] ELSE A]
  /\ pos = 1
  /\ \E c \in Values : candidate = c
  /\ cnt = 0

Scan ==
  /\ pos <= bound
  /\ LET x == seq[pos] IN
       \/ (cnt = 0 /\ candidate' = x /\ cnt' = 1)
       \/ (x = candidate /\ cnt' = cnt + 1)
       \/ (x # candidate /\ cnt' = cnt - 1)
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Scan]_Vars
  /\ WF_Vars(Scan) /\ WF_Vars([][Scan]_Vars)

Correct == pos = bound + 1 => \A c \in Values : (2 * Cardinality({i \in 1..bound : seq[i] = c}) > bound) => c = candidate

Inv == /\ TypeOK
  /\ pos \in 0..bound
  /\ cnt \in 0..bound

\* The bounded sequence operator replaces the standard Seq from Sequences so the
\* state space stays finite.  It is never declared or redefined here.
BoundedSeq == [i \in 1..bound |-> seq[i]]

====