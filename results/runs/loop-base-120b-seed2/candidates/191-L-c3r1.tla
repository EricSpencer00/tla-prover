---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Disk(i) == 2 ^ i                     \* size of the i‑th disk, i = 0..D-1
Disks   == { Disk(i) : i \in 0..D-1 }

\* Test whether a disk d (= 2^i) is present on a tower value t
DiskPresent(t, d) == (t % (2 * d) >= d)

\* Test whether a tower t has no disk smaller than d (i.e. all lower bits zero)
NoSmaller(t, d) == (t % d = 0)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* ----------------------------------------------------------------------
\* Moves
\* ----------------------------------------------------------------------
Move ==
    \E s, t \in 1..N :
        s # t /\
        \E i \in 0..D-1 :
            LET d == Disk(i) IN
                /\ DiskPresent(towers[s], d)        \* the disk is on the source
                /\ NoSmaller(towers[s], d)          \* it is the smallest on source
                /\ NoSmaller(towers[t], d)          \* destination has no smaller disk
                /\ towers' = [towers EXCEPT
                                 ![s] = towers[s] - d,
                                 ![t] = towers[t] + d]

Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < (2 ^ D)

Inv ==
    /\ Sum({ towers[i] : i \in 1..N }) = (2 ^ D) - 1

=============================================================================