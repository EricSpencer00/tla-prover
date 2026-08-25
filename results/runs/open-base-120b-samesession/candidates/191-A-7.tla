---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* Disk representation
\* ----------------------------------------------------------------------
DiskVals == { 2^(i-1) : i \in 1..D }   \* set of disk sizes (powers of two)

\* ----------------------------------------------------------------------
\* State variable: towers[i] is a natural number encoding the disks on
\* tower i (1..N) as a bitmask.
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper predicates for bitwise tests using arithmetic.
\* A disk d is present on tower t iff the bit corresponding to d is 1.
\* Since d is a power of two, (t \div d) % 2 = 1 tests that bit.
\* ----------------------------------------------------------------------
DiskOn(t, d) == (t \div d) % 2 = 1

NoSmallerOn(t, d) == 
  \A d2 \in DiskVals : d2 < d => (t \div d2) % 2 = 0

SmallestOn(t, d) == DiskOn(t, d) /\ NoSmallerOn(t, d)

\* ----------------------------------------------------------------------
\* Initial state: all disks on the first tower, others empty.
\* ----------------------------------------------------------------------
Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]
  /\ TypeOK

\* ----------------------------------------------------------------------
\* Type correctness: each tower value is a natural < 2^D.
\* ----------------------------------------------------------------------
TypeOK ==
  \A i \in 1..N : towers[i] \in Nat /\ towers[i] < 2^D

\* ----------------------------------------------------------------------
\* Conservation invariant: total sum of bits equals 2^D - 1.
\* ----------------------------------------------------------------------
Inv ==
  \* Sum of all tower values equals the sum of all disks.
  ( \* use the built‑in Sum operator \*)
  Sum(i \in 1..N, towers[i]) = 2^D - 1

\* ----------------------------------------------------------------------
\* Next-state relation: a legal move of the smallest disk on a source
\* tower to a destination tower where it will not land on a smaller disk.
\* ----------------------------------------------------------------------
Next ==
  \E src \in 1..N, dst \in 1..N :
    /\ src # dst
    /\ \E d \in DiskVals :
        /\ SmallestOn(towers[src], d)
        /\ NoSmallerOn(towers[dst], d)
        /\ towers' = [towers EXCEPT
                        ![src] = towers[src] - d,
                        ![dst] = towers[dst] + d]

\* ----------------------------------------------------------------------
\* Specification: standard init and always‑next with stuttering.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* SPECIFICATION   -> Spec
\* INVARIANTS      -> TypeOK, Inv
\* ----------------------------------------------------------------------
====