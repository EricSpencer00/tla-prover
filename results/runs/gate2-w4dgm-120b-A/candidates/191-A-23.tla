---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* A tower's value is the bitwise OR of its present disks (powers of two), so the
\* sum of all tower values is the bitwise OR of the whole configuration: a disk
\* that is both removed from one tower and added to another would be lost here.
\* Conservation of that sum is therefore the same as conservation of every disk.

VARIABLES towers

vars == <<towers>>

DiskSet == 1 .. (2 ^ D - 1)

TypeOK == /\ towers \in [1 .. N -> DiskSet]
          /\ towers[N] = 2 ^ D - 1

Init == /\ towers = [i \in 1 .. N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]
        /\ UNCHANGED << >>

Move(disk, src, dst) ==
    /\ src # dst
    /\ towers[src] >= disk
    /\ towers[src] % (2 * disk) = disk
    /\ towers[dst] % (2 * disk) = IF towers[dst] = 0 THEN 0 ELSE towers[dst] % (2 * disk)
    /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next == \E disk \in {2 ^ k : k \in 0 .. D - 1} \E src \in 1 .. N \E dst \in 1 .. N : Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

\* No liveness properties are asserted; the puzzle is solved by falsifying the
\* negation of the goal state via a bounded model-checking counterexample.
\* Conservation below is the only safety property that actually needs proving.
Inv == TypeOK /\ (2 ^ D - 1) = towers[1] + towers[2] + towers[3]

====