---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are sums of disk values; each disk is a distinct power of two
\* so the tower sum is exactly the bitwise-OR of the disks stacked on it.
\* Conservation of the whole-stack sum is what makes the bitwise encoding
\* safe: a move that duplicated or lost a disk would change the total.

VARIABLES tower

vars == <<tower>>

OnTower(d, t) == (tower[t] \div d) % 2 = 1

TypeOK ==
  /\ tower \in [1..N -> 0..(2 ^ D - 1)]

Init ==
  /\ tower = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

\* To pick the smallest disk on a tower, the bits below it must all be zero;
\* that is exactly what the bitwise AND test is checking here.
ValidMove(d, src, dst) ==
  /\ src # dst
  /\ OnTower(d, src)
  /\ (tower[src] % (2 * d)) = d
  /\ (tower[dst] % (2 * d)) = 0

Move(d, src, dst) ==
  /\ ValidMove(d, src, dst)
  /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]
  /\ UNCHANGED << >>

Next ==
  \E d \in {1 << k : k \in 0..(D - 1)} : \E src, dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: every disk is always somewhere, so the stack total is fixed.
Inv ==
  \A t \in 1..N : tower[t] \in 0..(2 ^ D - 1)
  /\ (tower[1] + tower[2] + tower[3]) = 2 ^ D - 1

====