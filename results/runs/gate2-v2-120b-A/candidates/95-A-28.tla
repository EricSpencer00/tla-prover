---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N \* grid dimension, to be supplied in the .cfg

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Indices == 1 .. N

CellPos == [i \in Indices, j \in Indices] \* a record representing a grid coordinate

Neighbors == {
    <<di, dj>> \in {-1,0,1} \X {-1,0,1} :
        ~(di = 0 /\ dj = 0)
}

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLE grid

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for the TypeOK invariant)
\* ----------------------------------------------------------------------
CellVals == BOOLEAN

TypeOK == grid \in [CellPos -> CellVals]

\* ----------------------------------------------------------------------
\* Initial state: each cell is chosen nondeterministically to be alive or dead
\* ----------------------------------------------------------------------
Init ==
    /\ grid = [pos \in CellPos |-> FALSE] \* start with all dead
    /\ \A pos \in CellPos:
          grid[pos] \in {TRUE, FALSE} \* trivial, but keeps the assignment explicit
    /\ \E f \in [CellPos -> CellVals]:
          grid = f

\* ----------------------------------------------------------------------
\* Helper: count live neighbors of a given position, treating out‑of‑bounds as dead
\* ----------------------------------------------------------------------
LiveNeighbors(pos) ==
    LET i == pos[i],
        j == pos[j] IN
    Cardinality({
        <<ni, nj>> \in CellPos :
            /\ (ni, nj) # (i, j)
            /\ (ni, nj) \in CellPos
            /\ grid[ni, nj] = TRUE
            /\ (ni - i) \in {-1,0,1}
            /\ (nj - j) \in {-1,0,1}
    })

\* ----------------------------------------------------------------------
\* Update rule for a single cell
\* ----------------------------------------------------------------------
NextCellAlive(pos) ==
    LET n == LiveNeighbors(pos) IN
    IF grid[pos] = TRUE THEN
        (* live cell survives with 2 or 3 neighbors *)
        n = 2 \/ n = 3
    ELSE
        (* dead cell becomes alive with exactly 3 neighbors *)
        n = 3

\* ----------------------------------------------------------------------
\* Tick action: simultaneous update of the whole grid
\* ----------------------------------------------------------------------
Tick ==
    /\ grid' = [pos \in CellPos |-> NextCellAlive(pos)]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Tick

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* The invariant required by the .cfg
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====