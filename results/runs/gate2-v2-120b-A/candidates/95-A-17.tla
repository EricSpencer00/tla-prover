---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension (positive integer)

\* Set of valid indices (1..N)
Idx == 1..N

\* State variable: mapping each (row, col) to a Boolean (TRUE = alive, FALSE = dead)
VARIABLE grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Neighbors(p) ==
    LET row == p[1] IN
    LET col == p[2] IN
    { <<r, c>> : r \in row-1 .. row+1,
                  c \in col-1 .. col+1,
                  (r # row \/ c # col) /\ r \in Idx /\ c \in Idx }

AliveNeighbors(p) ==
    Cardinality({ q \in Neighbors(p) : grid[q] })

\* ----------------------------------------------------------------------
\* Initial predicate: each cell nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
    /\ grid \in [Idx \X Idx -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Next-state relation: simultaneous update according to Game of Life rules
\* ----------------------------------------------------------------------
Next ==
    LET newGrid == [p \in Idx \X Idx |-> 
                       IF grid[p] 
                          THEN /\ (AliveNeighbors(p) = 2) \/ (AliveNeighbors(p) = 3)
                               TRUE
                          ELSE /\ (AliveNeighbors(p) = 3)
                               TRUE ] 
    IN  /\ grid' = newGrid

\* ----------------------------------------------------------------------
\* Full specification (including stuttering)
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Type-correctness invariant: grid is always a total mapping from positions
\* to Boolean values.
\* ----------------------------------------------------------------------
TypeOK ==
    grid \in [Idx \X Idx -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Temporal property (required by the .cfg) – the main spec
\* ----------------------------------------------------------------------
PROPERTY Spec

=============================================================================