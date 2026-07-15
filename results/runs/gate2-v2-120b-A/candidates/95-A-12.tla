---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension (to be supplied in the .cfg)

\* ----------------------------------------------------------------------
\* State variable: mapping each position (i,j) with 1 <= i,j <= N to a Bool
\* True  = cell is alive
\* False = cell is dead
\* ----------------------------------------------------------------------
VARIABLE grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Rows == 1..N
Cols == 1..N
Positions == Rows \X Cols

Neighbors(pos) ==
    LET i == pos[1] IN
    LET j == pos[2] IN
    { <<i + di, j + dj>> :
        di \in {-1,0,1} /\ dj \in {-1,0,1} /\
        ~(di = 0 /\ dj = 0) /\ 
        1 <= i + di /\ i + di <= N /\
        1 <= j + dj /\ j + dj <= N }

LiveNeighborCount(pos) ==
    Cardinality({ p \in Neighbors(pos) : grid[p] })

\* ----------------------------------------------------------------------
\* Initialization: each cell nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
    /\ grid \in [Positions -> BOOLEAN]

\* ----------------------------------------------------------------------
\* The deterministic evolution rule (Tick)
\* ----------------------------------------------------------------------
Next ==
    /\ grid' = [pos \in Positions |-> 
                IF grid[pos] THEN
                    LiveNeighborCount(pos) \in {2,3}
                ELSE
                    LiveNeighborCount(pos) = 3]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_grid

\* ----------------------------------------------------------------------
\* Type correctness invariant (required INVARIANT)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Positions -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Theorem (optional, not required by the .cfg but useful for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====