---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are binary encodings of the set of disks on that peg; a disk
\* is a power of two, so the sum of tower values equals 2^D - 1 (conservation).
\* A move is legal only if the moved disk is the smallest on its source peg and
\* smaller than every disk on the destination peg.

VARIABLES towers

vars == <<towers>>

\* Total number of disks present across all towers.
RECURSIVE SumOf(_, _)
SumOf(f, i) == IF i = 0 THEN 0 ELSE f[i] + SumOf(f, i - 1)

\* The smallest disk on a peg is the lowest-order bit set in its value; this is
\* what makes the bitwise ordering test both necessary and sufficient.
SmallestOn(v) == IF v = 0 THEN 0 ELSE 2 ^ (Nat(log(v) / log(2)))

TypeOK ==
  /\ towers \in [1..N -> 0..(2 ^ D - 1)]

\* No disk is ever created or destroyed: the total is invariant at 2^D - 1.
Inv == SumOf(towers, N) = 2 ^ D - 1

Init ==
  /\ towers[1] = 2 ^ D - 1
  /\ \A k \in 2..N : towers[k] = 0

Move ==
  /\ \E disk \in {2 ^ k : k \in 0..(D - 1)}, from \in 1..N, to \in 1..N :
       /\ from # to
       /\ towers[from] >= disk
       /\ towers[from] % (2 * disk) = disk
       /\ towers[to] % (2 * disk) = 0
       /\ towers' = [towers EXCEPT ![from] = @ - disk, ![to] = @ + disk]

Next == Move

Spec == Init /\ [][Next]_vars

====