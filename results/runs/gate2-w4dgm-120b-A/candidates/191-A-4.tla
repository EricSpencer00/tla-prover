---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES tower

vars == <<tower>>

\* Disk values are powers of two; a tower's value encodes the set of disks it holds
Disk(k) == 2 ^ k

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN Disk(x) + SumOf(S \ {x})

\* Conservation: the bitwise encoding must account for every disk exactly once
TotalDisks == SumOf(1 .. (D - 1))

TypeOK ==
  /\ tower \in [1 .. N -> 0 .. TotalDisks]
  /\ TotalDisks \in Nat

\* The puzzle is solved when every disk sits on the last tower
Goal == (tower[N] = TotalDisks)

Init ==
  /\ tower = [i \in 1 .. N |-> IF i = 1 THEN TotalDisks ELSE 0]

\* A move is legal if the disk is present on the source and is the smallest there,
\* and the destination has no smaller disk below it
Move(dk, s, t) ==
  /\ s # t
  /\ dk \in 1 .. TotalDisks
  /\ dk # 0
  /\ (tower[s] % (2 * dk)) = dk
  /\ (tower[t] % (2 * dk)) = 0
  /\ tower' = [tower EXCEPT ![s] = @ - dk, ![t] = @ + dk]

Next ==
  \E dk \in 1 .. TotalDisks : \E s \in 1 .. N : \E t \in 1 .. N : Move(dk, s, t)

Spec == Init /\ [][Next]_vars

\* Safety: disks are conserved and tower values stay natural
Inv == TypeOK /\ (tower[1] + tower[2] + tower[3] = TotalDisks)

====