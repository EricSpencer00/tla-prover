---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

K == 2 ^ D

VARIABLES tower

vars == <<tower>>

Ball == { 2 ^ i : i \in 0 .. (D - 1) }

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

\* Bitwise AND of two natural numbers: true iff every disk set in both towers
\* is at least as large as the smallest set disk on the left operand.
BitwiseAnd(a, b) ==
  IF a = 0 \/ b = 0 THEN TRUE
  ELSE LET i == CHOOSE k \in 0 .. (D - 1) : (a) % (2 ^ (k + 1)) >= 2 ^ k IN (b % (2 ^ (i + 1))) < 2 ^ i

TypeOK == /\ tower \in [1 .. N -> 0 .. (K - 1)]
          /\ SumOver(tower, 1 .. N) = K - 1

Init ==
  /\ tower = [i \in 1 .. N |-> IF i = 1 THEN K - 1 ELSE 0]

Move(d, from, to) ==
  /\ d \in Ball
  /\ from # to
  /\ (tower[from] % (2 * d)) = d
  /\ BitwiseAnd(tower[from], d)
  /\ BitwiseAnd(tower[to], d)
  /\ tower' = [tower EXCEPT ![from] = @ - d, ![to] = @ + d]

Next == \E d \in Ball, from, to \in 1 .. N : Move(d, from, to)

Spec == Init /\ [][Next]_vars

Inv == TRUE

====