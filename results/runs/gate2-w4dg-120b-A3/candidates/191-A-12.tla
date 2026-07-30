---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are natural numbers whose binary representations encode the
\* disks present on that tower (bit k means disk size 2^k is there).
Towers == 1..N

VARIABLES tower
vars == <<tower>>

\* A disk is a power of two; the smallest-on-source test looks at lower bits.
\* Bitwise AND is expressed as multiplication by 2^k and testing for zero.
PowerOfTwo(k) == 1 << k
SUM == (1 << D) - 1

TypeOK ==
  /\ tower \in [Towers -> 0..SUM]

\* No disks are created or destroyed: the tower values always add to SUM.
Inv ==
  /\ LET add[f \in SUBSET Towers] ==
         IF f = {} THEN 0
         ELSE LET x == CHOOSE e \in f : TRUE
              IN tower[x] + add[f \ {x}]
     IN add[Towers] = SUM

Init ==
  /\ tower = [t \in Towers |-> IF t = 1 THEN SUM ELSE 0]

\* The smallest disk on the source tower is the lowest set bit in its value.
Smallest(t) == tower[t] % 2

Move(d, src, dst) ==
  /\ src # dst
  /\ (tower[src] /\ d) = d
  /\ Smallest(src) = 1
  /\ (tower[dst] /\ (d - 1)) = 0
  /\ tower' = [tower EXCEPT ![src] = tower[src] - d, ![dst] = tower[dst] + d]

Next ==
  \/ \E k \in 0..(D - 1), src \in Towers, dst \in Towers : Move(PowerOfTwo(k), src, dst)

Spec == Init /\ [][Next]_vars

====