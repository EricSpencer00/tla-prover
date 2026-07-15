---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension, supplied by the .cfg

VARIABLE grid \* Mapping from each position (i,j) to a Boolean (TRUE = alive, FALSE = dead)

\* ----------------------------------------------------------------------
\* Type definition for positions
Pos == 1 .. N

\* ----------------------------------------------------------------------
\* Helper to describe the set of all grid coordinates
Coords == [i \in Pos |-> i] \X [j \in Pos |-> j]

\* ----------------------------------------------------------------------
\* Initial state: each cell is nondeterministically alive or dead
Init ==
    /\ grid \in [Coords -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Neighbor counting
Neighbors(i, j) ==
    {[i2, j2] \in Coords :
        i2 # i \/ j2 # j /\ 
        i2 \in i-1 .. i+1 /\ 
        j2 \in j-1 .. j+1}

LiveNeighbors(i, j) ==
    Cardinality({ [i2, j2] \in Neighbors(i, j) : grid[i2, j2] })

\* ----------------------------------------------------------------------
\* Deterministic update rule (Tick)
Next ==
    \E newGrid \in [Coords -> BOOLEAN] :
        /\ newGrid = [c \in Coords |-> 
                IF (grid[c] /\ (LiveNeighbors(c[1], c[2]) \in {2,3})) \/ 
                   (~grid[c] /\ LiveNeighbors(c[1], c[2]) = 3)
                THEN TRUE ELSE FALSE]
        /\ grid' = newGrid

\* ----------------------------------------------------------------------
\* Specification formula required by the cfg
Spec ==
    Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Type invariant required by the cfg
TypeOK ==
    grid \in [Coords -> BOOLEAN]

\* ----------------------------------------------------------------------
\* The name the .cfg expects for the overall specification
====