---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 1 /\ N \in Nat /\ N >= 2

Towers == 0 .. (N - 1)
Disks == { 1 << k : k \in 0 .. (D - 1) }

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOf(S \ { x })

Total == SumOf(Disks)

VARIABLES tower

vars == <<tower>>

TypeOK == /\ tower \in [ Towers -> 0 .. (Total) ]
          /\ \A t \in Towers : tower[t] >= 0 /\ tower[t] <= Total

\* Conservation of the physical quantity: the binary-encoded tower contents
\* across the whole board always sum to the fixed total, so no disk is ever
\* created or destroyed by a move.
Inv == SumOf( { tower[t] : t \in Towers } ) = Total

Init == tower = [ t \in Towers |-> IF t = 0 THEN Total ELSE 0 ]

Move(d, src, dst) ==
  /\ d \in Disks
  /\ src \in Towers
  /\ dst \in Towers
  /\ src # dst
  /\ tower[src] >= d
  /\ (tower[src] % (2 * d)) = d
  /\ (tower[dst] = 0 \/ (tower[dst] % (2 * d)) = 0)
  /\ tower' = [ tower EXCEPT ![src] = @ - d, ![dst] = @ + d ]

Next == \E d \in Disks, src \in Towers, dst \in Towers : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* No separate liveness requirement (the spec has none); the puzzle solution
\* is demonstrated by a counterexample to the negated goal.
Goal == \A t \in Towers : (t = (N - 1)) => (tower[t] = Total)

====