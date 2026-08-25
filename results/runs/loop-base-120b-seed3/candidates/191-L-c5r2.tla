---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* DiskSet: the set of disks, each represented by a distinct power of two
\* ----------------------------------------------------------------------
DiskSet == { 2 ^ k : k \in 0..(D - 1) }

\* ----------------------------------------------------------------------
\* State variable: towers[i] is the integer encoding of disks on tower i
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper: test whether disk d is present on tower value t
\* ----------------------------------------------------------------------
DiskPresent(t, d) == ((t \div d) % 2) = 1

\* ----------------------------------------------------------------------
\* Helper: d is the smallest disk on tower i (no smaller disk present)
\* ----------------------------------------------------------------------
SmallestOn(i, d) ==
    DiskPresent(towers[i], d) /\
    \A e \in DiskSet : e < d => ~DiskPresent(towers[i], e)

\* ----------------------------------------------------------------------
\* Helper: destination tower j can receive disk d (no smaller disk present)
\* ----------------------------------------------------------------------
CanReceive(j, d) ==
    \A e \in DiskSet : e < d => ~DiskPresent(towers[j], e)

\* ----------------------------------------------------------------------
\* Initialization: all disks on the first tower, others empty
\* ----------------------------------------------------------------------
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = (2 ^ D) - 1
    /\ \A i \in 2..N : towers[i] = 0

\* ----------------------------------------------------------------------
\* Next-state relation: move the smallest disk from a source tower to a
\* destination tower, respecting the Hanoi rules
\* ----------------------------------------------------------------------
Next ==
    \E i, j \in 1..N :
        /\ i # j
        /\ \E d \in DiskSet :
            /\ SmallestOn(i, d)
            /\ CanReceive(j, d)
            /\ towers' = [towers EXCEPT
                            ![i] = towers[i] - d,
                            ![j] = towers[j] + d]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* Type correctness invariant: each tower value is a natural number less
\* than 2^D
\* ----------------------------------------------------------------------
TypeOK == \A i \in 1..N : towers[i] \in 0..((2 ^ D) - 1)

\* ----------------------------------------------------------------------
\* Conservation invariant: total sum of tower values equals 2^D - 1
\* ----------------------------------------------------------------------
Inv == (\SUM i \in 1..N: towers[i]) = (2 ^ D) - 1

====