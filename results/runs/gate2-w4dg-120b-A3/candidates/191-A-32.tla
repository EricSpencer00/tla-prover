---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Disks == { 2 ^ k : k \in 0 .. (D - 1) }

VARIABLES tower

vars == <<tower>>

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN tower[x] + SumOf(S \ {x})

OnTower(d, t) == (tower[t] \land d) = d

SmallestOn(t) ==
  LET v == tower[t] IN
    IF v = 0 THEN 1
    ELSE 2 ^ (NATURAL(v) % 2) * 2 ^ (CHOOSE k \in 0 .. (D - 1) : (v \div 2 ^ k) % 2 = 1)

NoSmallerOn(t, d) ==
  LET v == tower[t] IN
    IF d = 1 THEN TRUE
    ELSE ((v \land (d - 1)) = 0)

TypeOK ==
  /\ tower \in [1 .. N -> 0 .. (2 ^ D - 1)]
  /\ SumOf(1 .. N) = 2 ^ D - 1

Init ==
  /\ tower = [t \in 1 .. N |-> IF t = 1 THEN 2 ^ D - 1 ELSE 0]

Move(d, src, dst) ==
  /\ src # dst
  /\ d \in Disks
  /\ OnTower(d, src)
  /\ src \in 1 .. N
  /\ dst \in 1 .. N
  /\ OnTower(SmallestOn(src), src)
  /\ NoSmallerOn(dst, d)
  /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \/ \E d \in Disks, src \in 1 .. N, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

====