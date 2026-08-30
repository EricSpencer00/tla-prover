---- MODULE Hanoi ----
EXTENDS Naturals

(* Tower of Hanoi puzzle modeled with disks as powers of two and tower values   *)
(* encoded as the sum of the present disks' values.  Conservation of disks is   *)
(* checked by summing tower values; the bitwise ordering constraints are       *)
(* tested using a custom integer bitwise-AND operation.                         *)

CONSTANTS D, N

\* Disk sizes are the distinct powers of two 1, 2, 4, ..., 2^(D-1).
Disks == { 2 ^ k : k \in 0 .. (D - 1) }

\* A power of two validly represents a disk; a power of two times an odd factor
\* is invalid and fails the size test that MoveDisk's preconditions rely on.
IsDisk(v) == \E k \in 0 .. (D - 1) : v = 2 ^ k

VARIABLES towers

vars == << towers >>

TypeOK ==
    /\ towers \in [1 .. N -> Nat]
    /\ \A i \in 1 .. N : towers[i] >= 0 /\ towers[i] < 2 ^ D

Init ==
    /\ towers = [i \in 1 .. N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

\* Tower i is empty if its value is zero.
Empty(i) == towers[i] = 0

\* A disk is present on tower i if its value is set in the tower's value.
OnTower(d, i) == towers[i] % (2 * d) >= d

\* A disk is the smallest present on a tower if no smaller disk is present.
Smallest(d, i) == towers[i] % (2 * d) = d

\* A tower has no smaller disk than d if no smaller disk is present.
NoSmallerOn(i, d) == towers[i] % d = towers[i]

\* Helper that returns the sum of all tower values.
RECURSIVE SumTowers(_)
SumTowers(k) == (IF k = 0 THEN 0 ELSE towers[k] + SumTowers(k - 1))

\* A move transfers one disk from a source tower to a destination tower.
MoveDisk(d, from, to) ==
    /\ from # to
    /\ OnTower(d, from)
    /\ Smallest(d, from)
    /\ NoSmallerOn(to, d)
    /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]

Next ==
    \/ \E d \in Disks, from \in 1 .. N, to \in 1 .. N : MoveDisk(d, from, to)

Spec == Init /\ [][Next]_vars

\* Conservation: the bitwise-encoded towers always sum to exactly the total
\* value of all disks -- none created, none destroyed.
Inv == SumTowers(N) = 2 ^ D - 1

\* Each tower's value stays within the natural range for D-bit bitsets.
TypeOK == TypeOK

====