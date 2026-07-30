---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 1 /\ N \in Nat /\ N >= 2

Total == 2 ^ D - 1

VARIABLES tower

vars == <<tower>>

\* The i-th tower is encoded as a natural number whose binary digits
\* indicate which power-of-two disks are on it.  The sum of all tower
\* values is constant, because each move subtracts the disk from the
\* source tower and adds it to the destination tower.
Sum == tower[1] + tower[2] + tower[3]

TypeOK == Sum \in 0..Total /\ \A i \in 1..N : tower[i] \in 0..Total

Init == tower = [i \in 1..N |-> IF i = 1 THEN Total ELSE 0]

\* Bitwise AND (implemented arithmetically) is used to test presence of
\* a disk and to enforce smallest-disk ordering constraints.
BitAnd(a, b) == (a + b - (a \ominus b)) \div 2

Move(d, s, t) ==
  /\ s # t
  /\ d \in {2 ^ k : k \in 0..(D - 1)}
  /\ tower[s] >= d
  /\ BitAnd(tower[s], d - 1) = 0
  /\ BitAnd(tower[t], d - 1) = 0
  /\ tower' = [tower EXCEPT ![s] = @ - d, ![t] = @ + d]

Next == \E d \in {2 ^ k : k \in 0..(D - 1)} : \E s \in 1..N : \E t \in 1..N : Move(d, s, t)

Spec == Init /\ [][Next]_vars

Inv == Sum = Total

====