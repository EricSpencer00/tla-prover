---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N

VARIABLE grid

(*-----------------------------------------------------------------
  Positions on the N-by-N grid
-----------------------------------------------------------------*)
Pos == (1..N) \X (1..N)

(*-----------------------------------------------------------------
  Neighbor relation (including diagonals, excluding the cell itself)
-----------------------------------------------------------------*)
IsNeighbor(p, q) ==
  /\ p # q
  /\ Abs(p[1] - q[1]) <= 1
  /\ Abs(p[2] - q[2]) <= 1

(*-----------------------------------------------------------------
  Number of live (TRUE) neighbors of a position p in a given grid g
-----------------------------------------------------------------*)
LiveNeighbors(g, p) ==
  Cardinality({ q \in Pos : IsNeighbor(p, q) /\ g[q] })

(*-----------------------------------------------------------------
  Initial state: any assignment of TRUE/FALSE to each cell
-----------------------------------------------------------------*)
Init ==
  grid \in [Pos -> BOOLEAN]

(*-----------------------------------------------------------------
  Simultaneous update of all cells according to the Game of Life rules
-----------------------------------------------------------------*)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF grid[p] 
        THEN (LiveNeighbors(grid, p) = 2) \/ (LiveNeighbors(grid, p) = 3)
        ELSE LiveNeighbors(grid, p) = 3
     ]

(*-----------------------------------------------------------------
  Type invariant: grid is always a total function from Pos to BOOLEAN
-----------------------------------------------------------------*)
TypeOK ==
  grid \in [Pos -> BOOLEAN]

vars == <<grid>>

Spec ==
  Init /\ [][Next]_vars

====