---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two; a tower's value is the sum of its disks,
\* and binary bits encode which disks are present -- smallest disk is bit 0.
\* Conservation is the per-disk accounting identity the puzzle rests on.

VARIABLES tower

vars == <<tower>>

TypeOK == /\ tower \in [1..N -> 0..(2^D) - 1]
          /\ \A i \in 1..N : tower[i] >= 0

Init == tower = [i \in 1..N |-> IF i = 1 THEN (2^D) - 1 ELSE 0]

\* Move the smallest disk out of src to a taller tower dst, where 'disk'
\* is the power-of-two value being moved.
Move == \E src \in 1..N, dst \in 1..N, disk \in {2^k : k \in 0..(D - 1)} :
           /\ src # dst
           /\ (tower[src] >= disk)
           /\ ((tower[src] \div disk) % 2 = 1)      \* src's smallest disk is disk
           /\ ((tower[dst] % (2 * disk) = 0) \/ (tower[dst] = 0))
           /\ tower' = [tower EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

\* Conservation: every move shifts a disk from one tower to another, so the
\* sum of tower values never changes; disks are neither created nor lost.
Conservation == (tower[1] + tower[2] + tower[3]) = (2^D) - 1

Spec == Init /\ [][Move]_vars

====