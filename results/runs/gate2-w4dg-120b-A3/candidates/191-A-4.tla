---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

MaxScore == 2 ^ D - 1

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN x + SumOver(S \ {x})

VARIABLES tower

vars == <<tower>>

TypeOK ==
  /\ tower \in [1 .. N -> 0 .. (2 ^ D - 1)]

Init ==
  /\ tower = [t \in 1 .. N |-> IF t = 1 THEN (2 ^ D - 1) ELSE 0]

MaskOn(t, k) == (tower[t] \div (2 ^ k)) % 2 = 1

HigherBitsZero(t, k) == (tower[t] % (2 ^ k)) = 0

Move ==
  \/ \E k \in 0 .. (D - 1), i, j \in 1 .. N :
       /\ i # j
       /\ mask = 2 ^ k
       /\ tower[i] >= mask
       /\ MaskOn(i, k)
       /\ HigherBitsZero(i, k)
       /\ HigherBitsZero(j, k)
       /\ tower' = [tower EXCEPT ![i] = @ - mask, ![j] = @ + mask]
  \/ UNCHANGED vars

Next == Move

Spec == Init /\ [][Next]_vars

Inv == SumOver({tower[t] : t \in 1 .. N}) = MaxScore

====