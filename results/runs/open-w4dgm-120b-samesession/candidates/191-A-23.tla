---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Blocks == { 2 ^ k : k \in 0 .. (D - 1) }

VARIABLES tower

vars == <<tower>>

TypeOK ==
  /\ tower \in [1 .. N -> 0 .. (2 ^ D - 1)]
  /\ (2 ^ D - 1) \in Nat

\* Conservation: every disk is in exactly one tower; the bitwise encoding never
\* creates or destroys a disk, only relocates it.
Conserved == (tower[1] + tower[2] + tower[3] = 2 ^ D - 1)

Init ==
  /\ tower = [i \in 1 .. N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

Move(d, src, dst) ==
  /\ src # dst
  /\ (tower[src] \in Blocks) \/ (\E k \in 0 .. (D - 1) : d = 2 ^ k /\ d \in Blocks)
  /\ (tower[src] \div d) % 2 = 1
  /\ (tower[src] \div (d * 2)) % 2 = 0
  /\ (tower[dst] = 0 \/ (tower[dst] \div d) % 2 = 0)
  /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in 1 .. (2 ^ D - 1) : \E src, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* The bitwise encoding is type-correct: every tower's value stays in Nat and in
\* the proper range; the conservation check is separate.
Inv == TypeOK /\ Conserved

====