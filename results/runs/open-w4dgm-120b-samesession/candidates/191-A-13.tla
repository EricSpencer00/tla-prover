---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are the bitwise-or of the powers-of-two disk sizes they hold.
\* Conservation then means the sum of all tower values is the full set of bits.
\* Moves are the only thing that change tower values, adding the disk to one and
\* subtracting it from the other.

VARIABLES towers
vars == <<towers>>

TypeOK ==
  /\ towers \in [1..N -> 0..(2^D - 1)]

RECURSIVE SumOver(_, _)
SumOver(f, S) == IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE
                      IN f[x] + SumOver(f, S \ {x})

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

Move(d, src, dst) ==
  /\ src # dst
  /\ d \in (1..(2^D - 1)) \ {0}
  /\ (d * 2) \notin (1..(2^D - 1))
  /\ (towers[src] \in (d - 1)..(2^D - 1))
  /\ d <= towers[dst]
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in (1..(2^D - 1)) : \E src \in 1..N : \E dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ SumOver(towers, 1..N) = 2^D - 1
  /\ TypeOK
====