---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }
M == 3

VARIABLES seq, i, cand, cnt
vars == <<seq, i, cand, cnt>>

Init ==
  /\ seq = << >>
  /\ i = 1
  /\ cand = 0
  /\ cnt = 0

Add(v) ==
  /\ Len(seq) < bound
  /\ seq' = Append(seq, v)
  /\ UNCHANGED <<i, cand, cnt>>

Vote ==
  /\ i <= Len(seq)
  /\ IF cnt = 0
       THEN cand' = seq[i]
       ELSE cand' = cand
  /\ IF cnt = 0 \or seq[i] = cand
       THEN cnt' = cnt + 1
       ELSE cnt' = cnt - 1
  /\ i' = i + 1
  /\ UNCHANGED seq

Decide ==
  /\ i > Len(seq)
  /\ Len(seq) > 0
  /\ cnt >= 2
  /\ seq' = << >>
  /\ i' = 1
  /\ cand' = 0
  /\ cnt' = 0

Next == \E v \in Value : Add(v) \/ Vote \/ Decide

Spec == Init /\ [][Next]_vars

Result == IF Len(seq) > 0 /\ cnt >= 2 THEN cand ELSE 0
=============================================================================