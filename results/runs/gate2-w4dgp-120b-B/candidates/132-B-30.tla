---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \notin Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

vars == <<seq, i, cand, cnt>>

Init ==
  /\ seq = <<>>
  /\ i = 0
  /\ cand = A
  /\ cnt = 0

Append(v) ==
  /\ i < bound
  /\ seq' = [seq EXCEPT ![i + 1] = v]
  /\ i' = i + 1
  /\ cand' = IF cnt = 0 THEN v ELSE cand
  /\ cnt' = IF v = cand THEN cnt + 1 ELSE cnt - 1

Next == \E v \in Value : Append(v)

Spec == Init /\ [][Next]_vars

Inv == \A i \in 1..Len(seq) : seq[i] \in Value

====