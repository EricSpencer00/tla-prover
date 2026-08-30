---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are sums of disk values (powers of two); a set bit means that
\* disk is present on the tower. Conservation is the sum of all tower values.
VARIABLES towers

vars == <<towers>>

TypeOK == towers \in [1..N -> 0..(2^D - 1)]

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN towers[x] + SumOver(S \ {x})

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]
  /\ UNCHANGED towers

\* A move is legal only if the disk is the smallest on its source tower and
\* the destination tower has no smaller disk already on it.
Move(d, src, dst) ==
  /\ src # dst
  /\ towers[src] >= d
  /\ towers[dst] + d < 2^D
  /\ (towers[src] % (2 * d)) = d
  /\ (towers[dst] % (2 * d)) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in {2^k : k \in 0..(D - 1)} : \E src \in 1..N : \E dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: every disk is accounted for exactly once across all towers.
Conservation == SumOver(1..N) = 2^D - 1

\* The goal state (all disks on the last tower) is not an invariant; its
\* negation is, so a counterexample trace shows the solution.
GoalNotReached == towers[N] # 2^D - 1

Inv == TypeOK /\ Conservation
====