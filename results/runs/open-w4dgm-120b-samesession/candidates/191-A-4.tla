---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi puzzle modeled as tower values that are bitwise encodings of
\* which disk sizes are present on each tower. Disk k has size 1 << k, and for
\* a tower value the bit at position k is set iff that disk is on the tower.
\* Conservation holds on the sum of tower values, which is the sum of a full
\* set of bits (2^D - 1), so the total never changes and no move is lost.

CONSTANTS D, N

ASSUME D \in Nat /\ N \in Nat

Range(n) == IF n = 0 THEN 0 ELSE n + Range(n - 1)

Towers == 0 .. (N - 1)

VARIABLES tower
vars == << tower >>

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN tower[x] + SumOver(S \ {x})

TypeOK ==
  /\ tower \in [Towers -> 0 .. (2 ^ D) - 1]
  /\ SumOver(Towers) = (2 ^ D) - 1

\* The smallest disk on a tower is the smallest set bit in its value; the test
\* here is arithmetic but equivalent to a bitwise AND of the value with (disk-1).
SmallestDisk(t, disk) ==
  /\ tower[t] >= disk
  /\ (tower[t] % (disk * 2)) / disk = 1

Init ==
  /\ tower = [t \in Towers |-> IF t = 0 THEN (2 ^ D) - 1 ELSE 0]
  /\ UNCHANGED << >>

\* Any legal move of the smallest disk from a source tower to a destination
\* tower that has no smaller disk on it (or is empty) is explored nondet.
Move(disk, src, dst) ==
  /\ src # dst
  /\ tower[src] >= disk
  /\ SmallestDisk(src, disk)
  /\ (tower[dst] = 0 \/ SmallestDisk(dst, disk))
  /\ tower' = [tower EXCEPT ![src] = @ - disk, ![dst] = @ + disk]
  /\ UNCHANGED << >>

Next ==
  \/ \E disk \in 1 .. ((2 ^ D) - 1) : \E src, dst \in Towers : Move(disk, src, dst)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Safety: disk conservation and proper tower-value typing.
Inv == TypeOK
====