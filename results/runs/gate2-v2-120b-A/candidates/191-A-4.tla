---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS D, N

\* Disk identifiers are powers of two: 1, 2, 4, ..., 2^(D-1)
DiskSet == { 2 ^ i : i \in 0..(D-1) }

\* The set of tower indices
TowerSet == 1..N

\* The zero value representing an empty tower
Zero == 0

\* The goal state: all disks on the last tower
Goal == [ i \in TowerSet |-> IF i = N THEN (2 ^ D) - 1 ELSE Zero ]

\* Initial state: all disks on the first tower
Init == 
    /\ vars = [ i \in TowerSet |-> IF i = 1 THEN (2 ^ D) - 1 ELSE Zero ]
    /\ Sum(vars) = (2 ^ D) - 1

\* Auxiliary operator: sum of all tower values
Sum(t) == 
    SUM i \in TowerSet: t[i]

\* Disk is the smallest present on tower t (i.e., no lower-order bits set)
SmallestOn(t, d) == 
    /\ d \in DiskSet
    /\ (t[i] = d) \/ (t[i] = Zero)        \* implicit in later checks
    /\ (t[i] # Zero) => (t[i] % (2 * d) = d)

\* Destination tower has no disk smaller than d
NoSmallerOn(t, d) ==
    /\ d \in DiskSet
    /\ (t[i] = Zero) \/ (t[i] % (2 * d) = 0)

\* A legal move from tower s to tower d moving disk mv
Move(s, d, mv) ==
    /\ s \in TowerSet
    /\ d \in TowerSet
    /\ s # d
    /\ mv \in DiskSet
    /\ (vars[s] >= mv)               \* mv could be present
    /\ (vars[s] % (2 * mv) = mv)     \* mv is the smallest on source
    /\ (vars[d] = Zero) \/ (vars[d] % (2 * mv) = 0)  \* dest has no smaller disk
    /\ vars' = [ vars EXCEPT ![s] = vars[s] - mv,
                               ![d] = vars[d] + mv ]
    /\ Sum(vars') = (2 ^ D) - 1

\* Next-state relation: nondeterministically choose any legal move
Next ==
    \E s \in TowerSet:
    \E d \in TowerSet:
    \E mv \in DiskSet:
        Move(s, d, mv)

\* Specification: Init and repeatedly apply Next
Spec ==
    Init /\ [][Next]_vars

\* Type correctness invariant
TypeOK ==
    /\ \A i \in TowerSet: vars[i] \in 0..((2 ^ D) - 1)
    /\ Sum(vars) = (2 ^ D) - 1

\* Safety invariant (the same as TypeOK for this model)
Inv ==
    TypeOK

\* Variable declaration required by TLC
vars \* will be declared in the .cfg file

====