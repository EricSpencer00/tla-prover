---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension, to be bound in the .cfg

\* ----------------------------------------------------------------------
\* State variable: mapping each position (i,j) in the N×N grid to a Boolean
\* indicating whether the cell is alive (TRUE) or dead (FALSE).
\* ----------------------------------------------------------------------
VARIABLE grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Pos == 1..N

Positions == { <<i, j>> : i \in Pos, j \in Pos }

Neighbors(p) ==
  LET i == p[1], j == p[2] IN
    { <<i2, j2>> :
        i2 \in Pos /\ j2 \in Pos /\ 
        (i2 # i \/ j2 # j) /\ 
        i2 >= i-1 /\ i2 <= i+1 /\ 
        j2 >= j-1 /\ j2 <= j+1 }

CellAlive(g, p) == g[p]

\* ----------------------------------------------------------------------
\* Initialization: each cell is nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
  /\ grid \in [Positions -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Deterministic update rule (Tick)
\* ----------------------------------------------------------------------
Next ==
  /\ UNCHANGED << >>
  /\ grid' = [p \in Positions |-> 
        LET aliveNeighbors == Cardinality({ q \in Neighbors(p) : CellAlive(grid, q) }) IN
          IF grid[p] THEN 
            aliveNeighbors = 2 \/ aliveNeighbors = 3
          ELSE
            aliveNeighbors = 3
      ]

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Positions -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* The module must expose the required identifiers
\* ----------------------------------------------------------------------
VARIABLES grid
\* (grid is already declared above; this line just makes the name visible)

\* Exported name for the configuration file
SpecSelf == Spec

=============================================================================