---- MODULE Hanoi ----
EXTENDS Naturals
\* A Tower of Hanoi model where each tower's value is the sum of its disks;
\* each disk is a distinct power of two, so a tower's bits encode its stack
\* and the smallest disk on a tower is its lowest set bit.
\* A single move action moves a disk from one tower to another, and the
\* conservation invariant checks that every move is a zero-sum transfer.
\* No liveness property is asserted; the solver must find the solution as
\* a counterexample to the negated goal.
\* Bitwise AND is supplied either by arithmetic or a Java override.

CONSTANTS D, N
\* D = number of disks (disk sizes are 2^0, 2^1, ..., 2^(D-1));
\* N = number of towers (pegs). They are modelled as constants.

Disks == 1..(2^D - 1)
\* All non-empty sums of the D distinct power-of-two disk sizes.
\* A tower value is always exactly one of these (or zero) because the
\* bitwise encoding never mixes bits between towers.

VARIABLES towers
\* towers[i] is the sum of the disk values resting on tower i.

vars == <<towers>>

RECURSIVE SumOver(_, _)
SumOver(f, k) == IF k = 1 THEN f[1] ELSE f[k] + SumOver(f, k - 1)

Total == SumOver(towers, N)
\* The invariant is applied to this derived quantity, not recomputed.

TypeOK == towers \in [1..N -> 0..(2^D - 1)]

Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* Move a disk from a tower to another tower under the Hanoi ordering
\* constraint: the source's smallest disk is moved, and the dest has no
\* smaller disk present.
Move(d, src, dst) ==
  /\ d IN Disks
  /\ src # dst
  /\ towers[src] >= d
  /\ towers[src] % (2 * d) = d
  /\ towers[dst] % (2 * d) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]
  /\ UNCHANGED << >>

Next == \E d \in Disks, src \in 1..N, dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: every move transfers a disk value between towers, so the
\* sum of all tower values is a fixed constant.
Inv == Total = 2^D - 1

====