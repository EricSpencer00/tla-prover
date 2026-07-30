---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi model: each tower's value is the sum of the disk values it
\* holds, where each disk is a distinct power of two.
\* Disk k has weight 2^k; "top" of a tower == smallest present disk (lowest set bit).
\* A single player moves one disk at a time from a source tower to a destination
\* tower, but only if the disk is the smallest on its source and the dest has no
\* smaller disk already, so a larger disk never lands on top of a smaller one.

CONSTANTS D, N

Towers == 1..N
Disks == { 2 ^ k : k \in 0..(D - 1) }

RECURSIVE SumUp(_)
SumUp(S) == IF S = {} THEN 0
            ELSE LET t == CHOOSE x \in S : TRUE
                 IN t + SumUp(S \ {t})

TotalWeight == 2 ^ D - 1

VARIABLES tvals

vars == << tvals >>

TypeOK == /\ tvals \in [Towers -> 0..TotalWeight]
          /\ TotalWeight \in Nat

Init == /\ tvals = [t \in Towers |-> IF t = 1 THEN TotalWeight ELSE 0]

MoveAny == \E d \in Disks, s \in Towers, dst \in Towers :
  /\ s # dst
  /\ (tvals[s] /\ d) = d
  /\ (tvals[s] % (2 * d)) = d
  /\ d <= tvals[dst]
  /\ (tvals[dst] % (2 * d)) = 0
  /\ tvals' = [tvals EXCEPT ![s] = @ - d, ![dst] = @ + d]

Next == MoveAny

Spec == Init /\ [][Next]_vars

\* Conservation: the sum of all tower values is invariant (no disk created/lost).
Inv == SumUp({tvals[t] : t \in Towers}) = TotalWeight

====