---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

CellSpace == 1 .. N
Positions == CellSpace \X CellSpace

\* The grid is represented as a function from each grid position to a boolean
\* value: TRUE = alive, FALSE = dead.
VARIABLES grid

vars == <<grid>>

\* Helper: the value of a cell outside the grid is always FALSE (dead).
Outside(p) == IF p[1] \in CellSpace /\ p[2] \in CellSpace THEN FALSE ELSE FALSE

\* Helper: number of live neighbors around a given cell position.
Neighbors(p) ==
    GridAlive([p[1] - 1 .. p[1] + 1] \X [p[2] - 1 .. p[2] + 1])
        - IF grid[p] THEN 1 ELSE 0

\* Helper: count live cells inside the grid over a finite set of positions.
GridAlive(S) == Cardinality({q \in S : q \in Positions /\ grid[q]})

TypeOK == grid \in [Positions -> BOOLEAN]

\* The initial grid is any possible assignment of live/dead to each cell.
Init == grid \in [Positions -> BOOLEAN]

\* The simultaneous update that constitutes one Game of Life generation:
\* each cell's fate is computed from the neighbor count in the *current*
\* generation, so the update is deterministic once the initial grid is fixed.
Tick == grid' = [p \in Positions |->
                    CASE Neighbors(p) = 3 -> TRUE
                         /\ (grid[p] => Neighbors(p) = 2 \/ Neighbors(p) = 3)
                         /\ (~grid[p] => Neighbors(p) = 3)
                         -> TRUE
                         [] (grid[p] /\ (Neighbors(p) < 2 \/ Neighbors(p) > 3))
                         -> FALSE
                         [] (~grid[p] /\ Neighbors(p) # 3) -> FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====