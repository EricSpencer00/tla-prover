---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Disk == 1 << D
Towers == 1..N

VARIABLES tower
vars == <<tower>>

RECURSIVE SumOf(_)
SumOf(k) == IF k = 0 THEN 0 ELSE tower[k] + SumOf(k - 1)

TypeOK ==
  /\ tower \in [Towers -> 0..(Disk - 1)]
  /\ SumOf(N) = Disk - 1

Init ==
  /\ tower = [k \in Towers |-> IF k = 1 THEN Disk - 1 ELSE 0]

Move(m, from, to) ==
  /\ from # to
  /\ tower[from] >= m
  /\ (tower[from] % (2 * m)) = m
  /\ (tower[to] % (2 * m)) = 0
  /\ tower' = [tower EXCEPT ![from] = @ - m, ![to] = @ + m]

Next ==
  \E m \in 1..(Disk - 1) : \E from \in Towers, to \in Towers : Move(m, from, to)

Spec == Init /\ [][Next]_vars

Goal == tower[N] = Disk - 1

PathGoal == (Goal => TRUE)
====