---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* Tower-of-Hanoi puzzle. TowerState[t] is a bitmask: bit k set <=> the
\* disk of size 2^k rests on tower t. All disks sit on the first tower at
\* start, and the conservation invariant protects the bitwise sum.
VARIABLES TowerState

TypeOK == TowerState \in [1..N -> 0..(2^D - 1)]

Init == TowerState = [t \in 1..N |-> IF t = 1 THEN 2^D - 1 ELSE 0]

\* A move is only legal for the top-most disk on a tower, and its destination
\* must be empty or hold no smaller disk (the bits below it are zero).
Move(d, s, e) ==
  /\ d \in {2^k : k \in 0..(D - 1)}
  /\ TowerState[s] >= d
  /\ s # e
  /\ (TowerState[s] % d = 0)
  /\ (TowerState[e] = 0 \/ TowerState[e] % d = 0)
  /\ TowerState' = [TowerState EXCEPT ![s] = @ - d, ![e] = @ + d]

Next == \E d \in {2^k : k \in 0..(D - 1)} \E s \in 1..N \E e \in 1..N : Move(d, s, e)

Spec == Init /\ [][Next]_<<TowerState>>

\* Conservation: the bit-counted disks are never created or destroyed.
Inv == LET f[S \in SUBSET (1..N)] ==
            IF S = {} THEN 0
            ELSE LET t == CHOOSE x \in S : TRUE IN TowerState[t] + f[S \ {t}]
        IN f[1..N] = 2^D - 1

====