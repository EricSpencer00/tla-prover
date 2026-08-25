---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
DiskSet == { 2^(i - 1) : i \in 1..D }

AllDisks == 2^D - 1

\* Is the disk d (a power of two) present on tower value t ?
IsPresent(t, d) == ((t \div d) % 2) = 1

\* Is d the smallest disk on a tower whose value is t ?
IsSmallest(t, d) == IsPresent(t, d) /\ (t % d = 0)

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Type correctness: each tower value is a natural < 2^D
\* ----------------------------------------------------------------------
TypeOK == /\ towers \in [1..N -> Nat]
          /\ \A i \in 1..N: towers[i] < 2^D

\* ----------------------------------------------------------------------
\* Conservation invariant: sum of all tower values equals AllDisks
\* ----------------------------------------------------------------------
Inv == Sum({ towers[i] : i \in 1..N }) = AllDisks

\* ----------------------------------------------------------------------
\* Initial state: all disks on the first tower, others empty
\* ----------------------------------------------------------------------
Init == /\ towers[1] = AllDisks
        /\ \A i \in 2..N: towers[i] = 0
        /\ TypeOK

\* ----------------------------------------------------------------------
\* One legal move
\* ----------------------------------------------------------------------
Move ==
  \E d \in DiskSet:
    \E s \in 1..N:
      \E t \in 1..N:
        /\ s # t
        /\ IsSmallest(towers[s], d)          \* d is on s and is the smallest there
        /\ (towers[t] % d = 0)                \* destination has no smaller disk
        /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                   ![t] = towers[t] + d]

Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

=============================================================================