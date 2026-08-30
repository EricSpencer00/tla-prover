---- MODULE Hanoi ----
\* Tower of Hanoi encoded as bitwise tower-state: a tower holds a natural number whose
\* set bits correspond to the disks (powers of two) currently on it. A move is legal when
\* the moving disk is present and is the smallest on its tower, and the destination has no
\* smaller disk. Conservation is encoded as the sum of tower values always being 2^D-1.
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS D, N

Towers == 1..N
Disks == { 2^k : k \in 0..(D - 1) }

VARIABLES occ

vars == <<occ>>

RECURSIVE Sum(_)
Sum(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN occ[x] + Sum(S \ {x})

TypeOK ==
  /\ occ \in [Towers -> 0..(2^D - 1)]
  /\ Sum(Towers) = 2^D - 1

Init ==
  /\ occ = [t \in Towers |-> IF t = 1 THEN 2^D - 1 ELSE 0]

Move(d, s, t) ==
  /\ occ[s] # 0
  /\ d \in Disks
  /\ occ[s] >= d
  /\ (occ[s] % (2 * d)) >= d
  /\ (t # s)
  /\ (occ[t] = 0 \/ (occ[t] % (2 * d)) = 0)
  /\ occ' = [occ EXCEPT ![s] = @ - d, ![t] = @ + d]

Next ==
  \/ \E d \in Disks, s \in Towers, t \in Towers : Move(d, s, t)

Spec == Init /\ [][Next]_vars

Inv == TypeOK
====