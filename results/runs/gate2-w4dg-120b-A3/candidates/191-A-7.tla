---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk k has size 2^k and is encoded as the bit value 2^k in a tower's sum.
Disks == { 2 ^ k : k \in 0 .. (D - 1) }

\* Sum of all tower values must always equal the full set of disks; this
\* constant represents the total.
Total == 2 ^ D - 1

TowerSum ==
  LET f[S \in SUBSET (0 .. (N - 1))] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN pegs[x] + f[S \ {x}]
  IN f[(0 .. (N - 1))]

\* Smallest disk on a tower: the lowest-order bit set in its sum, or zero if
\* the tower is empty. Needed to enforce the size ordering rule.
Smallest(t) ==
  LET rec(n) ==
        IF n = D THEN 0
        ELSE IF (pegs[t] % 2 = 1) THEN 1 << n
        ELSE rec(n + 1)
  IN rec(0)

TypeOK ==
  /\ pegs \in [0 .. (N - 1) -> 0 .. Total]
  /\ Total \in Nat

Init ==
  /\ pegs = [i \in 0 .. (N - 1) |-> IF i = 0 THEN Total ELSE 0]
  /\ UNCHANGED << >>

\* A move of a *single* smallest-possible disk from one tower to another.
Move(d, src, dst) ==
  /\ src # dst
  /\ d \in Disks
  /\ d <= pegs[src]
  /\ (pegs[src] % (d * 2)) = d
  /\ (pegs[dst] = 0 \/ (pegs[dst] % (d * 2)) = 0)
  /\ pegs' = [pegs EXCEPT ![src] = pegs[src] - d, ![dst] = pegs[dst] + d]
  /\ UNCHANGED << >>

Next == \E d \in Disks, src \in 0 .. (N - 1), dst \in 0 .. (N - 1) : Move(d, src, dst)

Spec == Init /\ [][Next]_<< pegs >>

\* Conservation: no disk is ever created or destroyed by a move.
Inv == TowerSum = Total

====