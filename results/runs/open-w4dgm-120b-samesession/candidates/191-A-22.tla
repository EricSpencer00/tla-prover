---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

\* tower k's value is the sum of the powers-of-two representing the disks
\* stacked on it (1, 2, 4, ...); the bit pattern encodes the set of present
\* disks. Conservation of that sum is the whole integrity argument.

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN towers[x] + SumOf(S \ {x})

SumTowers == SumOf(1 .. N)

Cap == (2 ^ D) - 1

TypeOK ==
  /\ towers \in [1 .. N -> 0 .. Cap]
  / SumTowers = Cap

Init ==
  /\ towers = [k \in 1 .. N |-> IF k = 1 THEN Cap ELSE 0]
  /\ SumTowers = Cap

On(t, d) == (towers[t] \div d) % 2 = 1

Move(d, src, dst) ==
  /\ src # dst
  /\ On(src, d)
  /\ \A m \in 1 .. D - 1 : m < d => ~On(src, m)
  /\ \A m \in 1 .. D - 1 : m < d => ~On(dst, m)
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]
  /\ SumTowers' = SumTowers

Next ==
  \E d \in 1 .. Cap : \E src, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* The goal is the inverse of an invariant: the system can reach a state where
\* the last tower carries the entire stack, so the negation of that goal must
\* be falsifiable to demonstrate the solution.
\* (No separate liveness property is declared; NOT_SPECIFIED is intentional.)
====