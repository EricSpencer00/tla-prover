---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PowerOfTwo(k) == 2 ^ k

Disks == { PowerOfTwo(k) : k \in 0..(D - 1) }

\* Test whether the bit corresponding to disk d (a power of two) is set in value v
BitSet(v, d) == (v % (2 * d)) >= d

\* The smallest disk on tower i (if any)
IsSmallest(i, d) ==
    /\ BitSet(towers[i], d)
    /\ \A e \in Disks : e < d => ~BitSet(towers[i], e)

\* Destination tower i may receive disk d (no smaller disk already present)
DestOk(i, d) ==
    \A e \in Disks : e < d => ~BitSet(towers[i], e)

\* Sum of all tower values
Sum(t) == \SUM i \in 1..N : t[i]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ towers[1] = 2 ^ D - 1
    /\ \A i \in 2..N : towers[i] = 0

\* ----------------------------------------------------------------------
\* Next-state relation (one legal move)
\* ----------------------------------------------------------------------
Move ==
    \E s, t \in 1..N :
        \E d \in Disks :
            /\ s # t
            /\ IsSmallest(s, d)
            /\ DestOk(t, d)
            /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
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
    /\ \A i \in 1..N : towers[i] < 2 ^ D

Inv == Sum(towers) = 2 ^ D - 1

====