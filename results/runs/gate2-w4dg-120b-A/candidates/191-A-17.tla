---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

Disk == { 2 ^ k : k \in 0 .. D - 1 }

VARIABLES towerVals

vars == << towerVals >>

RECURSIVE SumVals(_)
SumVals(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN towerVals[x] + SumVals(S \ {x})

InitialSum == (2 ^ D) - 1

TypeOK ==
  /\ towerVals \in [1 .. N -> 0 .. InitialSum]
  /\ SumVals(1 .. N) = InitialSum

Init ==
  /\ towerVals = [i \in 1 .. N |-> IF i = 1 THEN InitialSum ELSE 0]

SmallestOn(t) == \A k \in 0 .. D - 1 : (towerVals[t] % (2 * 2 ^ k)) \in {0, 2 ^ k}

Move(d, src, dst) ==
  /\ src # dst
  /\ src \in 1 .. N
  /\ dst \in 1 .. N
  /\ d \in Disk
  /\ (towerVals[src] /\ d) = d
  /\ SmallestOn(src)
  /\ (towerVals[dst] = 0 \/ SmallestOn(dst))
  /\ towerVals' = [towerVals EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in Disk, src \in 1 .. N, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

====