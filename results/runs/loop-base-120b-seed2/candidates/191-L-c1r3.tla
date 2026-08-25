---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS D, N

\*------------------------------------------------------------------------
\* Disk representation as powers of two
\*------------------------------------------------------------------------
Disk == { 2^i : i \in 0..(D-1) }

AllDisksValue == (2^D) - 1

\*------------------------------------------------------------------------
\* State variable: towers[i] is the sum of disk values on tower i
\*------------------------------------------------------------------------
VARIABLES towers

\*------------------------------------------------------------------------
\* Helper predicates for bitwise reasoning using arithmetic
\*------------------------------------------------------------------------
IsPresent(v, d) == (v \div d) % 2 = 1

NoSmaller(v, d) == \A d2 \in Disk : d2 < d => (v \div d2) % 2 = 0

IsSmallest(v, d) == IsPresent(v, d) /\ NoSmaller(v, d)

\*------------------------------------------------------------------------
\* Initial state: all disks on the first tower
\*------------------------------------------------------------------------
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = AllDisksValue
    /\ \A i \in 1..N : (i # 1) => towers[i] = 0

\*------------------------------------------------------------------------
\* Next-state relation: a legal move of the smallest disk on a tower
\*------------------------------------------------------------------------
Next ==
    \E src \in 1..N :
      \E dst \in 1..N :
        \E d \in Disk :
          /\ src # dst
          /\ IsSmallest(towers[src], d)
          /\ NoSmaller(towers[dst], d)
          /\ towers' = [towers EXCEPT
                          ![src] = towers[src] - d,
                          ![dst] = towers[dst] + d]

\*------------------------------------------------------------------------
\* Specification
\*------------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\*------------------------------------------------------------------------
\* Invariant: type correctness
\*------------------------------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2^D

\*------------------------------------------------------------------------
\* Invariant: conservation of total disk value
\*------------------------------------------------------------------------
Inv ==
    /\ \A i \in 1..N : towers[i] \in Nat
    /\ SUM i \in 1..N: towers[i] = AllDisksValue

\*------------------------------------------------------------------------
\* Theorem (optional) that Spec implies the invariants
\*------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv

====