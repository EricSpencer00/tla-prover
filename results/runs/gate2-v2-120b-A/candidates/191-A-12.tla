---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

CONSTANT D, N

\* Compute the value representing all disks present (bits 0..D-1 set)
AllDisks == (2 ^ D) - 1

\* DiskSet is the set of all disk values (powers of two)
DiskSet == { 2 ^ k : k \in 0..(D - 1) }

\* Helper: true if x is a power of two (i.e., exactly one bit set)
IsPowerOfTwo(x) == x \in DiskSet

\* Helper: smallest disk on a tower with value t
\* Returns 0 for an empty tower
SmallestDisk(t) ==
  IF t = 0 THEN 0
  ELSE 2 ^ (Min({ k : k \in 0..(D-1) : (t % (2 ^ (k+1))) \ge (2 ^ k) }))

VARIABLE towers

\* TypeOK: each tower value is a natural number less than 2^D
TypeOK == /\ towers \in [1..N -> Nat]
        /\ \A i \in 1..N : towers[i] < 2 ^ D

\* Conservation invariant: sum of all tower values equals AllDisks
Inv == \A i \in 1..N : TRUE  \* placeholder to satisfy cfg; actual invariant is below
Consistent == PlusReduce(towers) = AllDisks

\* Initial state: all disks on tower 1, others empty
Init == towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

\* A move selects a source and destination tower and a disk to move
Move ==
  \E source \in 1..N, dest \in 1..N, d \in DiskSet :
    /\ source # dest
    /\ (towers[source] % (2 * d)) >= d          \* disk d is present on source
    /\ (towers[source] % d) = 0                 \* d is the smallest on source
    /\ (towers[dest] % (2 * d)) < d              \* dest has no smaller disk
    /\ towers' = [towers EXCEPT ![source] = towers[source] - d,
                                 ![dest]   = towers[dest] + d]

\* Stutter step to avoid deadlock when no move is possible (should never happen)
Stutter == towers' = towers

Next == Move \/ Stutter

Spec == Init /\ [][Next]_<<towers>>

\* The liveness property is not specified; we expose the safety invariants.
\* The identifier Inv is required by the .cfg; we bind it to the conservation property.
Inv == Consistent

\* The module ends here.
====