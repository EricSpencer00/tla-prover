---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS D, N

VARIABLES towers

\* --------------------------------------------------------------
\* Set of disks, each represented as a distinct power of two
\* --------------------------------------------------------------
Disk == { 2 ^ (i - 1) : i \in 1..D }

\* -----------------------------------------------------------------
\* Helper predicates using arithmetic to test presence of a disk
\* -----------------------------------------------------------------
DiskPresent(d, v) == ((v \div d) % 2) = 1

IsSmallest(d, v) ==
    DiskPresent(d, v) /\ 
    \A e \in Disk : e < d => ~DiskPresent(e, v)

\* -----------------------------------------------------------------
\* Initial state: all disks on tower 1, others empty
\* -----------------------------------------------------------------
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* -----------------------------------------------------------------
\* A legal move of the smallest disk from src to dst
\* -----------------------------------------------------------------
Move ==
    \E src, dst \in 1..N :
        /\ src # dst
        /\ \E d \in Disk :
            /\ IsSmallest(d, towers[src])
            /\ \A e \in Disk : e < d => ~DiskPresent(e, towers[dst])
            /\ towers' = [towers EXCEPT 
                            ![src] = towers[src] - d,
                            ![dst] = towers[dst] + d]

Next == Move

\* -----------------------------------------------------------------
\* Type correctness: each tower value is a natural < 2^D
\* -----------------------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] \in 0..((2 ^ D) - 1)

\* -----------------------------------------------------------------
\* Conservation invariant: sum of all tower values is 2^D - 1
\* -----------------------------------------------------------------
Inv ==
    (\Sum i \in 1..N : towers[i]) = (2 ^ D) - 1

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Vars == <<towers>>
Spec == Init /\ [][Next]_Vars

=============================================================================