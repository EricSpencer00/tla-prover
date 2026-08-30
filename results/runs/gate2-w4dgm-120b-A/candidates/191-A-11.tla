---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are sums of disk values (powers of two); a disk is present
\* on a tower exactly when its bit is set in that tower's value.
VARIABLES towers

vars == <<towers>>

\* Helper: apply a bitmask to a tower value, clearing the bits that mask
\* clears and leaving the others unchanged.
Shifted(mask, val) == mask * (val \div mask)

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]
  /\ UNCHANGED towers

\* A legal move: the disk must be present, must be the smallest on the
\* source tower, and the destination must have no smaller disk on it.
Move(disk, src, dst) ==
  /\ disk \in {2 ^ k : k \in 1..D}
  /\ src # dst
  /\ (towers[src] % (2 * disk) >= disk
  /\ towers[dst] % (2 * disk) = 0
  /\ towers' = [towers EXCEPT ![src] = Shifted(disk, @) - disk, ![dst] = Shifted(disk, @) + disk]
  /\ UNCHANGED <<>>

Next == \E disk \in 1..(2 ^ D - 1), src \in 1..N, dst \in 1..N : Move(disk, src, dst)

Goal == towers[N] = (2 ^ D) - 1

TypeOK == \A i \in 1..N : towers[i] \in 0..((2 ^ D) - 1)

Inv == (\Sum_{i \in 1..N} towers[i]) = (2 ^ D) - 1

Spec == Init /\ [][Next]_vars

====