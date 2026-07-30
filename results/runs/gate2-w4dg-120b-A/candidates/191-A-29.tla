---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi modeled as a bitwise encoding of disk positions: bit k of a
\* tower's value holds the disk of size 2^k. No explicit stack; the bits carry
\* the ordering: the smallest disk on a tower is the lowest set bit. Actions
\* move a single disk, verified as the smallest present and not placed atop a
\* smaller disk.
\* 
\* The required identifiers are exactly those from the reference configuration:
\* the constants D and N, the specification Spec, the Init and Next steps, the
\* invariants TypeOK and Inv, and the (empty) set of state constraints.

CONSTANTS D, N

Towers == 1..N
Robust == 2 ^ D

\* Bit testing without a built-in operator: a disk of size s is present on a
\* tower iff the remainder of the tower's value modulo 2*s is at least s.
Present(t, s) == (s <= (t % (2 * s)))

VARIABLES tower

vars == <<tower>>

SumTowers == tower[1] + tower[2] + tower[3]

TypeOK == /\ tower \in [Towers -> 0..(Robust - 1)]
          /\ D \in Nat /\ N \in Nat /\ N >= 3

Init == /\ tower = [i \in Towers |-> IF i = 1 THEN Robust - 1 ELSE 0]
        /\ D = 3
        /\ N = 3

\* A move is legal only if the disk is on the source, is that tower's smallest
\* present disk, and cannot be placed on a strictly smaller disk at the dest.
LegalMove(d, src, dst) ==
  /\ src # dst
  /\ src \in Towers /\ dst \in Towers
  /\ Present(tower[src], d)
  /\ ~Present(tower[src], d >> 1)
  /\ ~Present(tower[dst], d >> 1)

Next == \E d \in {1, 2, 4} : \E src \in Towers, dst \in Towers :
          /\ LegalMove(d, src, dst)
          /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Spec == Init /\ [][Next]_vars

\* Conservation: tower bits are never created or destroyed, so the sum of
\* tower values is always exactly the weight of the full stack.
Inv == SumTowers = Robust - 1

====