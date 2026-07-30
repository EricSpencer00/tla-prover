---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk values are powers of two: bit k of a tower's value corresponds to the
\* disk of size 2^k. Tower values are summed, not kept as sets.
Disk(i) == 2^i

VARIABLES tower
vars == <<tower>>

\* Tower values sum to the full set of disks iff the puzzle has neither created
\* nor destroyed any disk.
Total == tower[1] + tower[2] + tower[3]

TypeOK ==
  /\ tower \in [1..N -> 0..(2^D - 1)]
  /\ Total = 2^D - 1

Init ==
  /\ tower[1] = 2^D - 1
  /\ tower[2] = 0
  /\ tower[3] = 0

\* A move is legal only if the disk is on the source tower and is the smallest
\* disk there, and the destination tower has no smaller disk.
LegalMove(disk, from, to) ==
  /\ from # to
  /\ (tower[from] /\ disk) = disk
  /\ (tower[from] % (2 * disk)) = disk
  /\ (tower[to] = 0 \/ (tower[to] % (2 * disk)) = 0)

Move(disk, from, to) ==
  /\ LegalMove(disk, from, to)
  /\ tower' = [tower EXCEPT ![from] = @ - disk, ![to] = @ + disk]
  /\ UNCHANGED <<>>

Next ==
  \/ \E i \in 0..(D - 1), from \in 1..N, to \in 1..N : Move(Disk(i), from, to)
  \/ UNCHANGED <<tower>>

\* No liveness: the entire solution is explored as a counterexample to the goal
\* being unreachable. Spec is a plain safety specification.
Spec == Init /\ [][Next]_vars

Inv == TypeOK
====