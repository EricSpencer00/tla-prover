---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi modeled as a bitwise occupancy register per tower.
\* Each disk has a size that is a distinct power of two; a tower's value is
\* the sum of the sizes of the disks it holds, so the bits set in the value
\* exactly encode which disks are present on that tower.

CONSTANTS D, N

\* Derived constants: the smallest and largest disk sizes, and the
\* bitmask covering all disks (all bits set).
Bottom == 1
Top == 2 ^ (D - 1)
AllMask == 2 ^ D - 1

\* The set of all legal disk values (powers of two up to 2^(D-1)) and the set
\* of all ordered source/destination tower pairs.
DiskValues == { 2 ^ k : k \in 0 .. (D - 1) }
Moves == { <<src, dst>> \in (1 .. N) \X (1 .. N) : src # dst }

VARIABLES towers
vars == <<towers>>

TypeOK == /\ towers \in [1 .. N -> 0 .. AllMask]
          /\ towers[1] \in [0 .. AllMask]
          /\ towers[N] \in [0 .. AllMask]

\* Conservation: every disk is accounted for exactly once somewhere across
\* all towers, because the sum of all tower values is the running sum of
\* the set of all disk values.
Inv == towers[1] + towers[N] = AllMask

Init == /\ towers = [i \in 1 .. N |-> IF i = 1 THEN AllMask ELSE 0]

\* A disk can be moved only if it is present on the source tower, it is the
\* smallest disk on that tower, and the destination tower has no smaller
\* disk (so it cannot be placed on top of a smaller one), or the destination
\* tower is empty.
Move(d, src, dst) == /\ d \in DiskValues
                     /\ <<src, dst>> \in Moves
                     /\ towers[src] >= d
                     /\ towers[src] % (2 * d) = d
                     /\ towers[dst] % (2 * d) \in {0, d}
                     /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in DiskValues, src \in 1 .. N, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

====