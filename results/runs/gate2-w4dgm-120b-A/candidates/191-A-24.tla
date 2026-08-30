---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two: 1, 2, 4, ... 2^(D-1). A tower's value is the
\* sum of the sizes of the disks standing on it, so its binary representation
\* encodes exactly which disks are present. Conservation is defined via the
\* sum of all tower values, not via an explicit stack model.
Disks == 1 << (0 .. (D - 1))

VARIABLES tower

vars == <<tower>>

TypeOK == /\ tower \in [1..N -> 0..(2^D - 1)]
          /\ D \in Nat /\ N \in Nat

RECURSIVE SumOf(_)
SumOf(S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE y \in S : TRUE IN tower[x] + SumOf(S \ {x})

Init == /\ tower = [t \in 1..N |-> IF t = 1 THEN (2^D - 1) ELSE 0]
        /\ UNCHANGED <<D, N>>

\* A legal move removes a disk from one tower and adds it to another. The
\* ordering constraints are bitwise: a disk may move only if it is the
\* smallest present on its source tower and no smaller disk sits on the
\* destination tower.
Move(d, s, t) == /\ tower[s] >= d /\ (tower[s] % (2 * d)) = d
                 /\ s # t /\ (tower[t] % (2 * d)) = 0
                 /\ tower' = [tower EXCEPT ![s] = @ - d, ![t] = @ + d]

Next == \E d \in Disks, s \in 1..N, t \in 1..N : Move(d, s, t)

Spec == Init /\ [][Next]_vars

\* Conservation: the total amount of disk "weight" across all towers never
\* changes -- no move ever creates or destroys a disk.
Conservation == SumOf(1..N) = 2^D - 1

\* Safety: type correctness of the tower values.
TowerValuesInRange == \A t \in 1..N : tower[t] \in 0..(2^D - 1)

====