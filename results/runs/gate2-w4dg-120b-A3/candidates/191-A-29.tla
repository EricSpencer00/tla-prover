---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers
vars == <<towers>>

Total == (2 ^ D) - 1
DiskValues == {2 ^ k : k \in 0 .. (D - 1)}
SumsTo == (N - 1) * Total

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

TypeOK ==
  /\ towers \in [1 .. N -> 0 .. SumsTo]
  /\ towers[1] = Total
  /\ \A i \in 1 .. N: i # 1 => towers[i] = 0

Init ==
  /\ towers = [i \in 1 .. N |-> IF i = 1 THEN Total ELSE 0]

ValidMove(d, src, dst) ==
  /\ d \in DiskValues
  /\ towers[src] >= d
  /\ (towers[src] \div d) % 2 = 1
  /\ \A s \in DiskValues: (s < d) => ((towers[src] \div s) % 2 = 0)
  /\ IF towers[dst] = 0 THEN TRUE
     ELSE \A s \in DiskValues: (s < d) => ((towers[dst] \div s) % 2 = 0)
  /\ towers[src] >= d

Move(d, src, dst) ==
  /\ src # dst
  /\ ValidMove(d, src, dst)
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]
  /\ UNCHANGED <<>>

Next ==
  \/ \E d \in DiskValues, src, dst \in 1 .. N: Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Conservation == SumOf(towers, 1 .. N) = Total

Inv == TypeOK /\ Conservation
====