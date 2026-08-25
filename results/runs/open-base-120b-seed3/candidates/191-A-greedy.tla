---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
MaxVal == 2 ^ D - 1

DiskSet == { 2 ^ (i - 1) : i \in 1..D }

(*--------------------------------------------------------------------
  Helper predicates for bitwise reasoning
--------------------------------------------------------------------*)
IsPresent(t, d) == ((t \div d) % 2) = 1
IsSmallest(t, d) == (t % d) = 0
NoSmaller(t, d) == (t % d) = 0

(*--------------------------------------------------------------------
  Initial state: all disks on tower 1
--------------------------------------------------------------------*)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN MaxVal ELSE 0]

(*--------------------------------------------------------------------
  Next-state relation: a legal move of a single disk
--------------------------------------------------------------------*)
Next ==
    \E d \in DiskSet, s \in 1..N, t \in 1..N :
        /\ s # t
        /\ IsPresent(towers[s], d)
        /\ IsSmallest(towers[s], d)
        /\ NoSmaller(towers[t], d)
        /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                   ![t] = towers[t] + d]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    towers \in [1..N -> Nat] /\
    \A i \in 1..N : towers[i] \in 0..MaxVal

Inv ==
    \Sum_{i \in 1..N} towers[i] = MaxVal

====