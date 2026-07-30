---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

\* Disk k has size 2^k (powers of two); a tower's value is the sum of the sizes of
\* the disks resting on it, so the binary representation of a tower's value
\* encodes exactly which disks are present there.
\* Bitwise AND therefore tests membership and ordering constraints.

\* Disk k is present on tower t iff the k-th bit of towers[t] is set.
Contains(t, k) == ((towers[t] \div 2^k) % 2) = 1

\* The smallest disk on a tower is its lowest set bit; a move requires the
\* source to have no smaller disk present.
Smallest(t, k) == Contains(t, k) /\ \A j \in 0..(k - 1) : ~Contains(t, j)

\* Destination must be empty or have no smaller disk than the one being moved.
DestOK(d, k) == d = 0 \/ \A j \in 0..(k - 1) : ~Contains(d, j)

TypeOK == towers \in [0..N-1 -> 0..(2^D) - 1]

\* Conservation: every disk is always somewhere, so the sum of tower values is
\* the sum of all disk sizes -- a fixed quantity -- and never changes.
Inv == (towers[0] + towers[1] + towers[2]) = (2^D) - 1

Init == towers = [t \in 0..N-1 |-> IF t = 0 THEN (2^D) - 1 ELSE 0]

\* A single move of one disk; nondeterministically chosen but subject to the
\* size-ordering constraints of the Tower of Hanoi puzzle.
Move(k, s, d) ==
    /\ Contains(s, k)
    /\ Smallest(s, k)
    /\ s # d
    /\ DestOK(d, k)
    /\ towers' = [towers EXCEPT ![s] = @ - 2^k, ![d] = @ + 2^k]

Next == \E k \in 0..D-1 : \E s \in 0..N-1 : \E d \in 0..N-1 : Move(k, s, d)

Spec == Init /\ [][Next]_vars

====