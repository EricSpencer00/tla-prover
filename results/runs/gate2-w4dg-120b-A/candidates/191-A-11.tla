---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* Tower is a map from tower index to a natural number whose binary bits encode
\* which disks are stacked there. A bit k set means disk of size 2^k is present.
Towers == [1..N -> 0..(2 ^ D) - 1]

VARIABLES tower

vars == <<tower>>

\* Sum of all tower values: the total number of disks (as bits) in the system.
RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

OnTower(t, k) == (tower[t] \land (2 ^ k)) = 2 ^ k
SmallestOn(t, k) == (tower[t] \mod (2 ^ (k + 1))) = 2 ^ k
NoSmallerOn(t, k) == (tower[t] \mod (2 ^ k)) = 0

TypeOK ==
  /\ tower \in Towers
  /\ SumOver(tower, 1..N) = (2 ^ D) - 1

Init ==
  /\ tower = [t \in 1..N |-> IF t = 1 THEN (2 ^ D) - 1 ELSE 0]

\* A move moves exactly one disk from src to dst, and only the smallest disk
\* on the source tower, onto a tower whose top disk is strictly larger.
Move(k, src, dst) ==
  /\ src # dst
  /\ src \in 1..N
  /\ dst \in 1..N
  /\ k \in 0..(D - 1)
  /\ OnTower(src, k)
  /\ SmallestOn(src, k)
  /\ NoSmallerOn(dst, k)
  /\ tower' = [tower EXCEPT ![src] = @ - (2 ^ k), ![dst] = @ + (2 ^ k)]

Next == \E k \in 0..(D - 1), src \in 1..N, dst \in 1..N : Move(k, src, dst)

Spec == Init /\ [][Next]_vars

\* No liveness is asserted; the puzzle's solution is witnessed by a counterexample
\* to the negation of the goal state (all disks on the last tower).
\* Hence the spec deliberately contains no temporal progress property.
Inv == TypeOK

====