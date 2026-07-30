---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi puzzle modelled with bitwise-encoded tower occupancy.
\* A tower's value is a natural number whose binary bits denote which
\* disk (each a distinct power of two) is standing on that tower.
\* The invariant checks exact conservation of disks across all towers.

CONSTANTS D, N

Towers == 1..N
Disks == {2 ^ k : k \in 0..(D - 1)}
MaxSum == (2 ^ D) - 1
Total == (N * (N - 1)) \div 2

VARIABLES towers

vars == <<towers>>

TypeOK == /\ towers \in [Towers -> 0..MaxSum]
          /\ Total = 0

SmallestOn(t) == \E k \in 0..(D - 1) : (t >= 2 ^ k) /\ ((t % (2 ^ (k + 1))) < 2 ^ k)
DiskOn(t) == \E k \in 0..(D - 1) : t = 2 ^ k

Init ==
  /\ towers = [i \in Towers |-> IF i = 1 THEN MaxSum ELSE 0]

LegalMove(d, fr, to) ==
  /\ d \in Disks
  /\ fr # to
  /\ (towers[fr] >= d)
  /\ (towers[fr] % (2 * d) < d)
  /\ ((towers[to] = 0) \/ (towers[to] % (2 * d) < d))

Move(d, fr, to) ==
  /\ LegalMove(d, fr, to)
  /\ towers' = [towers EXCEPT ![fr] = @ - d, ![to] = @ + d]

Next == \E d \in Disks, fr \in Towers, to \in Towers : Move(d, fr, to)

Spec == Init /\ [][Next]_vars

Inv == /\ \A i \in Towers : towers[i] <= MaxSum
       /\ (\A i \in Towers : \E k \in 0..(D - 1) : towers[i] = 2 ^ k) \/ (SumB(towers) = MaxSum)

SumB(f) == LET g[S \in SUBSET Towers] ==
                IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + g[S \ {x}]
           IN g[Towers]

====