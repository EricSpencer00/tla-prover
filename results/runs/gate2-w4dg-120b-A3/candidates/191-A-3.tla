---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two; tower state is the sum of present disk values.
\* A tower is empty iff its value is zero. Conservation holds in the encoded
\* representation because the sum of all towers is always 2^D - 1.

ASSUME D \in Nat /\ D >= 1 /\ N \in Nat /\ N >= 2

Disks == {2^k : k \in 0..(D - 1)}
LowBits(d) == d - 1

VARIABLES tower

vars == <<tower>>

RECURSIVE SumT(_)
SumT(S) == IF S = {} THEN 0
           ELSE LET x == CHOOSE y \in S : TRUE IN x + SumT(S \ {x})

Total == SumT({tower[i] : i \in 1..N})

TypeOK == \A i \in 1..N : tower[i] \in 0..(2^D - 1)

Init == tower = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

Move(d, src, dst) ==
  /\ src # dst
  /\ d \in Disks
  /\ (tower[src] /\ d) = d
  /\ (tower[src] /\ LowBits(d)) = 0
  /\ (tower[dst] /\ LowBits(d)) = 0
  /\ tower' = [tower EXCEPT ![src] = tower[src] - d, ![dst] = tower[dst] + d]

Next == \E d \in Disks, src \in 1..N, dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the disks are only ever moved between towers, never created
\* or destroyed, in the encoded representation as well as the concrete one.
Inv == Total = 2^D - 1

====