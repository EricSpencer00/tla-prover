---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower state is the sum of each present disk's size, and each size is a power of two.
\* Bitwise AND (implemented as a pure arithmetic operator here) is used to test
\* disk presence and ordering constraints.
\* No liveness property is asserted; the puzzle is solved by the invariant that
\* the final tower holds every disk.

VARIABLES towers

vars == << towers >>

RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

\* Binary-AND implemented arithmetically: test whether disk d (a power of two)
\* is present in the value v (an integer) without requiring native integer bitwise.
Contains(d, v) == ((v \ DIV d) % 2) = 1

Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* A move of disk d from tower s to tower t is legal iff d is on s, d is the
\* smallest disk on s, and t is empty or has no smaller disk than d.
Move(d, s, t) == /\ d >= 1 /\ (d & (d - 1)) = 0
                 /\ s # t
                 /\ Contains(d, towers[s])
                 /\ \A k \in 1..(d - 1) : ~Contains(k, towers[s])
                 /\ \A k \in 1..(d - 1) : ~Contains(k, towers[t])
                 /\ towers' = [towers EXCEPT ![s] = @ - d, ![t] = @ + d]

Next == \E d \in 1..(2^D - 1) : \E s \in 1..N : \E t \in 1..N : Move(d, s, t)

Spec == Init /\ [][Next]_vars

\* Conservation: the total weight of all disks is fixed.
Inv == SumOf(towers, 1..N) = 2^D - 1

TypeOK == \A i \in 1..N : towers[i] \in 0..(2^D - 1)

====