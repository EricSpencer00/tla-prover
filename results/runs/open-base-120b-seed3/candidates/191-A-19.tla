---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Disk representation
--------------------------------------------------------------------*)
DiskSet == { 2 ^ i : i \in 0..(D-1) }

MaxVal == 2 ^ D - 1

(*--------------------------------------------------------------------
  Helper predicates for bitwise tests (using arithmetic)
--------------------------------------------------------------------*)
Contains(t, d) == ((t \div d) % 2) = 1

SmallestOn(t, d) ==
    /\ Contains(t, d)
    /\ \A d2 \in DiskSet : d2 < d => ~Contains(t, d2)

NoSmallerOn(t, d) ==
    \A d2 \in DiskSet : d2 < d => ~Unless(Contains(t, d2), FALSE)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ towers[1] = MaxVal
    /\ \A i \in (2..N) : towers[i] = 0

(*--------------------------------------------------------------------
  Move action
--------------------------------------------------------------------*)
Move(disk, src, dst) ==
    /\ src # dst
    /\ src \in 1..N /\ dst \in 1..N
    /\ disk \in DiskSet
    /\ SmallestOn(towers[src], disk)
    /\ NoSmallerOn(towers[dst], disk)
    /\ towers' = [towers EXCEPT ![src] = towers[src] - disk,
                                 ![dst] = towers[dst] + disk]

Next ==
    \E disk \in DiskSet :
        \E src, dst \in 1..N : Move(disk, src, dst)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ \A i \in 1..N : towers[i] \in Nat
    /\ \A i \in 1..N : towers[i] <= MaxVal

Inv ==
    Sum(i \in 1..N : towers[i]) = MaxVal

====