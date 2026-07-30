---- MODULE Hanoi ----
EXTENDS Integers

CONSTANTS D, N

VARIABLES tower

vars == <<tower>>

RECURSIVE SumTower(_)
SumTower(k) == IF k = 0 THEN 0 ELSE tower[k - 1] + SumTower(k - 1)

RECURSIVE Bits(_)
Bits(n) == IF n = 0 THEN 0 ELSE (n % 2) + Bits(n \div 2)

MaskOf(k) == 2 ^ k

TypeOK ==
  /\ tower \in [1..N -> 0..(2 ^ D - 1)]

Init ==
  /\ tower = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

Move(d, src, dst) ==
  /\ src # dst
  /\ d <= 2 ^ D - 1
  /\ (d * 2) > (tower[src] % (2 * d))
  /\ (d * 2) > (tower[dst] % (2 * d))
  /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]
  /\ UNCHANGED << >>

Next == \E d \in {MaskOf(k) : k \in 0..(D - 1)} : \E src \in 1..N : \E dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ SumTower(N) = 2 ^ D - 1
  /\ \A i \in 1..N : tower[i] < 2 ^ D

====