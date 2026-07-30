---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower k holds the sum of its disks, each disk being a power of two. The
\* sum of all towers therefore equals 2^D-1, which is the conservation check.
Rings == 2 ^ D - 1

VARIABLES towers

vars == <<towers>>

\* Sum(towers) is the total over all N tower registers.
Sum(towers) ==
  LET add[S \in SUBSET 1..N] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN towers[x] + add[S \ {x}]
  IN add[1..N]

TypeOK == /\ towers \in [1..N -> 0..Rings]

Init ==
  /\ towers = [k \in 1..N |-> IF k = 1 THEN Rings ELSE 0]

\* Bitwise AND is implemented arithmetically so the model is pure TLA+; a
\* Java override could replace this with a true bitwise primitive.
AND(x, y) == IF x = 0 \/ y = 0 THEN 0 ELSE 2 ^ (Nat(log(x) : Nat) /\ Nat(log(y) : Nat))

\* A disk sits on a tower iff its bit is set in that tower's value.
OnTower(d, t) == AND(towers[t], d) = d

Move(d, from, to) ==
  /\ d \in {2 ^ k : k \in 0..(D - 1)}
  /\ from # to
  /\ OnTower(d, from)
  /\ \A s \in 1..N : s < from => ONTower(d, s)
  /\ \A s \in 1..N : s < to => ONTower(d, s)
  /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]

Next == \E d \in {2 ^ k : k \in 0..(D - 1)} : \E from \in 1..N : \E to \in 1..N : Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* Conservation: the sum of the tower registers always equals the packed set
\* of all disks, so no move ever creates or destroys a disk.
Inv == Sum(towers) = Rings

====