---- MODULE Hanoi ----
EXTENDS Naturals

\* The Tower of Hanoi model with a bitwise representation of disk positions.
\* D and N are constants (declared in the .cfg); all other operators are
\* required by the specification checklist and must appear exactly once.

CONSTANTS D, N

\* Disk k has size 2^k, so the size of the largest disk is the most significant
\* bit of the full-stack value (2^D - 1). A tower's value is the sum of the
\* sizes of the disks on it; because sizes are powers of two, the binary pattern
\* of the value is exactly the set of disks present.

Disks == 1 << D

VARIABLES towers

vars == <<towers>>

TypeOK ==
  /\ towers \in [1..N -> 0..(Disks - 1)]

Init ==
  /\ towers = [t \in 1..N |-> IF t = 1 THEN (Disks - 1) ELSE 0]

\* A disk is present on a tower if that tower's value has the corresponding
\* bit set; a tower's smallest disk is the least significant set bit.
OnDisk(d, t) == (towers[t] & d) = d
SmallerOn(t) == towers[t] - (towers[t] & (-towers[t]))
\* The least significant set bit of x is x & -x; subtracting it yields the
\* remainder, i.e. the sum of all strictly larger disks on the tower.

Move(d, src, dst) ==
  /\ src # dst
  /\ OnDisk(d, src)
  /\ SmallerOn(src) = 0
  /\ (towers[dst] = 0 \/ SmallerOn(dst) = 0)
  /\ towers' = [t \in 1..N |-> IF t = src THEN towers[t] - d
                                   ELSE IF t = dst THEN towers[t] + d
                                   ELSE towers[t]]
  /\ UNCHANGED <<D, N>>

Next ==
  \E d \in {1 << k : k \in 0..(D - 1)}:
    \E src \in 1..N:
      \E dst \in 1..N:
        Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the total of all tower values always equals the full stack,
\* so no disk is created or destroyed by any move.
Inv ==
  /\ TypeOK
  /\ (towers[1] + towers[2] + towers[3]) = (Disks - 1)
====