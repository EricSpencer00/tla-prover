---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* Tower i's value, in binary, encodes which disks (powers of two) sit on it.
VARIABLES towers

vars == <<towers>>

\* Helper: bitwise AND of two naturals via arithmetic (bit i is 1 iff 2^i <= x).
BitMask(i) == 2 ^ i

TypeOK ==
  /\ towers \in [1..N -> 0..(2 ^ D) - 1]
  /\ towers[1] >= 0 /\ towers[2] >= 0 /\ towers[3] >= 0

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]
  /\ UNCHANGED <<towers>>

\* A move: remove a disk from src and add it to dst, only if it is the smallest
\* disk on src and not larger than the smallest on dst.
Move(disk, src, dst) ==
  /\ src # dst
  /\ towers[src] >= disk
  /\ towers[src] \cap disk = disk
  /\ towers[src] \cap (disk - 1) = 0
  /\ towers[dst] \cap (disk - 1) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]
  /\ UNCHANGED <<towers>>

Next ==
  \E disk \in {BitMask(i) : i \in 0..(D - 1)}, src \in 1..N, dst \in 1..N:
    Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the bitwise encoding keeps the total disk value fixed.
Conservation ==
  towers[1] + towers[2] + towers[3] = (2 ^ D) - 1

\* The puzzle is solved when all disks sit on the last tower; its complement is
\* checked as an invariant in the spec below (a counterexample trace is the
\* solution).
Inv == towers[N] # (2 ^ D) - 1

====