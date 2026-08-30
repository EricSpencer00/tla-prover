---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi puzzle modeled with a bitwise tower state: each tower's value
\* is the sum of its present disk values (powers of two), so the binary
\* representation of a tower tells which disks sit on it. Conservation of disks
\* is the sum-of-tower-values invariant; the puzzle is solved (no counterexample
\* to the goal) when all disks reach the last tower.

CONSTANTS D, N

Disks == 1 << D
Towers == 1 .. N

VARIABLES towers

vars == <<towers>>

RECURSIVE SumTowers(_)
SumTowers(n) == IF n = 0 THEN 0 ELSE towers[n] + SumTowers(n - 1)

TypeOK ==
  /\ towers \in [Towers -> 0 .. (Disks - 1)]
  /\ SumTowers(N) = Disks - 1

Init ==
  /\ towers = [i \in Towers |-> IF i = 1 THEN Disks - 1 ELSE 0]
  /\ UNCHANGED <<>>

Move(disk, from, to) ==
  /\ from # to
  /\ disk \in {2^k : k \in 0 .. (D - 1)}
  /\ towers[from] >= disk
  /\ (towers[from] % (2 * disk)) = disk
  /\ (towers[to] % (2 * disk)) = 0
  /\ towers' = [towers EXCEPT ![from] = @ - disk, ![to] = @ + disk]

Next == \E disk \in {2^k : k \in 0 .. (D - 1)}, from, to \in Towers : Move(disk, from, to)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

====