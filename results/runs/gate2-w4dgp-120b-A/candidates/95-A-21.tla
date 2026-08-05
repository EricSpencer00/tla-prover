---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat \ {0}

Positions == 1..N
NeighborsP == [r : Positions, c : Positions]

VARIABLE grid
vars == <<grid>>

\* Fully deterministic evolution: the grid dimensions are fixed, and each
\* generation is computed directly from the previous one, so no nondeterministic
\* choice remains once the initial configuration is fixed.
RECURSIVE CountLive(_)
CountLive(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (IF grid[x] THEN 1 ELSE 0) + CountLive(S \ {x})

Neighbors(x) ==
  { y \in NeighborsP :
      (y.r # x.r \/ y.c # x.c) /\ (y.r >= x.r - 1 /\ y.r <= x.r + 1) /\ (y.c >= x.c - 1 /\ y.c <= x.c + 1) }

Init ==
  /\ grid \in [NeighborsP -> BOOLEAN]

Tick ==
  /\ grid' = [x \in NeighborsP |-> LET n == CountLive(Neighbors(x)) IN
                  IF grid[x] THEN (n = 2 \/ n = 3) ELSE (n = 3)]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [NeighborsP -> BOOLEAN]

====