---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \notin Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

Init ==
  /\ seq = [1 |-> A]
  /\ i = 1
  /\ cand = A
  /\ cnt = 1

Append(s) ==
  /\ i < bound
  /\ seq' = [seq EXCEPT ![i + 1] = s]
  /\ i' = i + 1
  /\ cand' = IF cnt = 0 THEN s ELSE cand
  /\ cnt' = IF cnt = 0 THEN 1 ELSE IF s = cand THEN cnt + 1 ELSE cnt - 1

Next ==
  \/ \E s \in Value : Append(s)

\* The candidate is a majority only of the scanned prefix, not of the whole.
MajorityScanned ==
  /\ cnt > 0
  /\ i >= 2
  /\ Cardinality({ j \in 1..i : seq[j] = cand }) * 2 > i

vars == <<seq, i, cand, cnt>>
Spec == Init /\ [][Next]_vars

====