---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS D, N

VARIABLES towers

\* Bitwise AND operator (custom implementation; may be overridden in Java)
\* Assume that BitAnd is defined elsewhere if needed
BitAnd == \* placeholder; actual implementation provided by an extension
\* For the purposes of invariants we can use the built-in `#` operator which is
\* defined in the standard library, but to keep the module self‑contained we
\* provide a simple arithmetic definition that works for natural numbers.
\* BitAnd(x, y) = 0 iff (x /\ y) = 0
BitAnd(x, y) == (x /\ y)

\* Helper: the size of a disk, given its bit position k (0‑based)
Disk(k) == 1 << k

\* Helper: the set of all disk values
Disks == { 1 << k : k \in 0..(D-1) }

\* Initial state: all disks on tower 1, others empty
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN (1 << D) - 1 ELSE 0]

\* Possible moves: choose a source tower, destination tower, and a disk k
Move ==
    \E src, dst \in 1..N :
        src # dst /\ \E k \in 0..(D-1) :
            \E diskVal \in Disks :
                diskVal = 1 << k /\ 
                towers[src] /\ diskVal = diskVal /\ (* disk present on src *)
                towers[src] = diskVal \/ \E lower \in 0..(k-1) : towers[src] /\ (1 << lower) = 0 /\ (* smallest on src *) 
                towers[dst] = 0 \/ (* dst empty *) 
                \E lower \in 0..(k-1) : towers[dst] /\ (1 << lower) = 0 /\ (* no smaller on dst *) 
                towers' = [towers EXCEPT
                             .[src] = towers[src] - diskVal,
                             .[dst] = towers[dst] + diskVal]

Next == Move

Spec ==
    Init /\ [][Next]_<<towers>>

\* Safety invariant: type correctness (each tower value < 2^D)
TypeOK ==
    \A i \in 1..N : towers[i] \in Nat /\ towers[i] < (1 << D)

\* Safety invariant: conservation of disk values
Inv ==
    \A i \in 1..N : towers[i] \in Nat /\ towers[i] < (1 << D) /\ 
    SUM i \in 1..N : towers[i] = (1 << D) - 1

====