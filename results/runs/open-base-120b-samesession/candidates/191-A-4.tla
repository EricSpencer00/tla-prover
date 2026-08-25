---- MODULE Hanoi ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* State variable: towers[i] is the bitwise encoding of disks on tower i
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
MaxVal == 2 ^ D - 1

DiskSet == { 2 ^ k : k \in 0 .. D - 1 }

\* ----------------------------------------------------------------------
\* Helper predicates for bitwise reasoning (using arithmetic)
\* ----------------------------------------------------------------------
IsOn(t, d) == ((t \div d) % 2) = 1

SmallestOn(t, d) ==
    /\ IsOn(t, d)
    /\ \A d2 \in DiskSet : d2 < d => ~IsOn(t, d2)

DestOK(dst, d) ==
    \A d2 \in DiskSet : d2 < d => ~IsOn(towers[dst], d2)

\* ----------------------------------------------------------------------
\* Initial state: all disks on the first tower
\* ----------------------------------------------------------------------
Init ==
    /\ towers = [i \in 1 .. N |-> IF i = 1 THEN MaxVal ELSE 0]

\* ----------------------------------------------------------------------
\* One legal move
\* ----------------------------------------------------------------------
Move ==
    \E d \in DiskSet :
        \E s \in 1 .. N :
            \E dst \in 1 .. N :
                /\ s # dst
                /\ IsOn(towers[s], d)
                /\ SmallestOn(towers[s], d)
                /\ DestOK(dst, d)
                /\ towers' = [towers EXCEPT
                                ![s]   = towers[s] - d,
                                ![dst] = towers[dst] + d]

Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<towers>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [1 .. N -> Nat]
    /\ \A i \in 1 .. N : towers[i] < 2 ^ D

\* ----------------------------------------------------------------------
\* Conservation invariant
\* ----------------------------------------------------------------------
Inv ==
    /\ \Sum i \in 1 .. N : towers[i] = MaxVal

====