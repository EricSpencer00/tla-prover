---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers
vars == <<towers>>

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumF(f, S \ {x})

RECURSIVE BitsBelow(_, _)
BitsBelow(v, k) ==
  IF k = 0 THEN 0
  ELSE (IF (v /\ 1) = 1 THEN 1 ELSE 0) + 2 * BitsBelow(v \div 2, k - 1)

TypeOK ==
  /\ towers \in [0 .. N - 1 -> 0 .. (2 ^ D) - 1]
  /\ SumF(towers, 0 .. N - 1) = (2 ^ D) - 1

Init ==
  /\ towers = [i \in 0 .. N - 1 |-> IF i = 0 THEN (2 ^ D) - 1 ELSE 0]

Move(d, src, dst) ==
  /\ d \in {2 ^ k : k \in 0 .. D - 1}
  /\ src # dst
  /\ (towers[src] /\ d) = d
  /\ BitsBelow(towers[src], D) = d
  /\ (towers[dst] = 0 \/ BitsBelow(towers[dst], D) = 0)
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \/ \E d \in {2 ^ k : k \in 0 .. D - 1}, src \in 0 .. N - 1, dst \in 0 .. N - 1 : Move(d, src, dst)
  \/ UNCHANGED towers

Spec == Init /\ [][Next]_vars

Inv == TypeOK

====