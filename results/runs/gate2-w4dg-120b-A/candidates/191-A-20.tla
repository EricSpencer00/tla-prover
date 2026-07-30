---- MODULE Hanoi ----
EXTENDS Naturals

\* A Tower of Hanoi puzzle. Disk positions are held in a per-tower bitfield:
\* a tower's value has bit k set iff the disk of size 2^k is on that tower.
\* Conservation is expressed on the integer sum of the tower values.
\* No liveness is asserted; the puzzle is solved by falsifying the goal
\* state as an invariant, which yields a counterexample trace.

CONSTANTS D, N

ASSUME D >= 2 /\ D <= 3 /\ N >= 2 /\ N <= 3

\* The value of a tower when all disks sit on it.
AllOnOne == 2 ^ D - 1

Towers == 1 .. N
DISKS == { 2 ^ k : k \in 0 .. (D - 1) }

VARIABLES tower

vars == << tower >>

TypeOK ==
  /\ tower \in [Towers -> Nat]
  /\ \A k \in Towers : tower[k] < 2 ^ D

Init ==
  /\ tower = [k \in Towers |-> IF k = 1 THEN AllOnOne ELSE 0]

\* Disk k is present on tower t iff the corresponding bit is set there.
OnTower(k, t) == (tower[t] \div k) % 2 = 1

\* A move is legal if the disk is on the source, is the smallest on that
\* source, and the destination has no smaller disk sitting on it.
LegalMove(k, src, dst) ==
  /\ src # dst
  /\ OnTower(k, src)
  /\ \A d \in DISKS : d < k => ~OnTower(d, src)
  /\ \A d \in DISKS : d < k => ~OnTower(d, dst)

Move(k, src, dst) ==
  /\ LegalMove(k, src, dst)
  /\ tower' = [tower EXCEPT ![src] = @ - k, ![dst] = @ + k]

Next ==
  \/ \E k \in DISKS, src \in Towers, dst \in Towers : Move(k, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the total encoded weight never changes.
Inv == tower[1] + tower[2] + (IF N = 3 THEN tower[3] ELSE 0) = AllOnOne

====