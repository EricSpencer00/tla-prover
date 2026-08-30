---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Bitwise AND operator, defined from scratch or via Java override.
And(x, y) == IF x = 0 \orelse y = 0 THEN 0 ELSE 2 * And(x \div 2, y \div 2) + IF (x % 2 = 1) /\ (y % 2 = 1) THEN 1 ELSE 0

\* Bits below k (mask for disks smaller than size 2^k).
BelowMask(k) == (1 \div 2) * (2^k - 1)

VARIABLES tower

vars == <<tower>>

TypeOK == /\ tower \in [1..N -> 0..(2^D - 1)]
          /\ \A i \in 1..N : tower[i] \in Nat /\ tower[i] < 2^D

Init == /\ tower = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

Move(d, src, dst) ==
  /\ src # dst
  /\ d \in { 2^k : k \in 0..(D - 1) }
  /\ And(tower[src], d) = d
  /\ And(tower[src], BelowMask(1 + d)) = 0
  /\ And(tower[dst], BelowMask(1 + d)) = 0
  /\ tower' = [tower EXCEPT ![src] = tower[src] - d, ![dst] = tower[dst] + d]

Next == \E d \in { 2^k : k \in 0..(D - 1) }, src \in 1..N, dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* The total disk value is a conserved quantity: nothing created or destroyed.
Conservation == tower[1] + tower[2] + tower[3] = 2^D - 1

\* Tower 3 is the goal: the negation of this invariant is the reachability
\* property that demonstrates the puzzle is solvable.
GoalComplete == tower[N] = 2^D - 1

Inv == TypeOK /\ Conservation

====