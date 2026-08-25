---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE grid

(*--------------------------------------------------------------------
  Set of all positions on the N×N grid
--------------------------------------------------------------------*)
Positions == { <<i, j>> : i \in 1..N, j \in 1..N }

(*--------------------------------------------------------------------
  Absolute value helper
--------------------------------------------------------------------*)
Abs(x) == IF x >= 0 THEN x ELSE -x

(*--------------------------------------------------------------------
  Neighbouring positions of a cell (excluding the cell itself)
--------------------------------------------------------------------*)
Neighbors(p) == { q \in Positions :
                    q # p /\ 
                    Abs(q[1] - p[1]) <= 1 /\ 
                    Abs(q[2] - p[2]) <= 1 }

(*--------------------------------------------------------------------
  Number of live neighbours of a cell in the current grid
--------------------------------------------------------------------*)
LiveNeighbors(p) == Cardinality({ q \in Neighbors(p) : grid[q] = TRUE })

(*--------------------------------------------------------------------
  Initialisation: any assignment of TRUE/FALSE to every cell
--------------------------------------------------------------------*)
Init == grid \in [Positions -> BOOLEAN]

(*--------------------------------------------------------------------
  One tick of the Game of Life (simultaneous update of all cells)
--------------------------------------------------------------------*)
Tick ==
    /\ \A p \in Positions :
          grid'[p] =
            IF ( grid[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3) )
               \/ ( ~grid[p] /\ LiveNeighbors(p) = 3 )
            THEN TRUE ELSE FALSE

(*--------------------------------------------------------------------
  Specification of the system
--------------------------------------------------------------------*)
Spec == Init /\ [][Tick]_grid

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeOK == grid \in [Positions -> BOOLEAN]

====