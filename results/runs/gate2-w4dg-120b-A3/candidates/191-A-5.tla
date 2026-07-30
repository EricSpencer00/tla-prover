---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES tower
vars == <<tower>>

RECURSIVE SumTower(_)
SumTower(n) == IF n = 0 THEN 0 ELSE tower[n] + SumTower(n - 1)

OnTower(d, t) == IF tower[t] = 0 THEN FALSE ELSE ((tower[t] \div d) * d) = tower[t]

SmallestOn(t, d) == (tower[t] % (2 * d) = d)

BitsLowClear(t, d) == (tower[t] % d) = 0

Init ==
  /\ tower = [t \in 1 .. N |-> IF t = 1 THEN 2 ^ D - 1 ELSE 0]
  /\ UNCHANGED <<>>

Move(d, src, dst) ==
  /\ d \in {2 ^ k : k \in 0 .. (D - 1)}
  /\ src # dst
  /\ OnTower(d, src)
  /\ SmallestOn(src, d)
  /\ (tower[dst] = 0 \/ BitsLowClear(dst, d))
  /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]
  /\ UNCHANGED <<>>

Next ==
  \/ \E d \in {2 ^ k : k \in 0 .. (D - 1)}. \E src \in 1 .. N. \E dst \in 1 .. N. Move(d, src, dst)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ tower \in [1 .. N -> 0 .. (2 ^ D - 1)]

Inv == SumTower(N) = 2 ^ D - 1

====