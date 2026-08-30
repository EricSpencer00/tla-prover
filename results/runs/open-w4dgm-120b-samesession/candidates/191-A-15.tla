---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower i's value is the sum of the powers-of-two (disk sizes) of the disks
\* stacked on it. The sum of all towers is therefore the sum of all disks.
\* Conservation: every move just moves a disk between towers, so that sum is
\* invariant.

VARIABLES towers

vars == <<towers>>

Disks == { 2 ^ k : k \in 0 .. (D - 1) }

\* Tower i has a smaller disk than d iff any lower-order bit of its value is set.
HasSmaller(i, d) == \E k \in 1 .. (D - 1) : (2 ^ k) >= d /\ (towers[i] % (2 ^ k) >= (2 ^ k) / 2)

SumTowers == towers[1] + towers[2] + towers[3]

TypeOK ==
  /\ towers \in [1 .. N -> 0 .. (2 ^ D) - 1]
  /\ SumTowers = (2 ^ D) - 1

Init ==
  /\ towers = (IF N >= 3 THEN [1 |-> (2 ^ D) - 1, 2 |-> 0, 3 |-> 0]
                         ELSE [i \in 1 .. N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0])

Move(d, from, to) ==
  /\ from # to
  /\ (towers[from] % (2 * d)) >= d
  /\ ~HasSmaller(from, d)
  /\ (towers[to] = 0 \/ ~HasSmaller(to, d))
  /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]

Next ==
  \E d \in Disks, from \in 1 .. N, to \in 1 .. N : Move(d, from, to)

Spec == Init /\ [][Next]_vars

Inv == TypeOK
====