---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension, supplied by the .cfg

\* ----- State variable -----
VARIABLES grid

\* ----- Types -----
CellPos == 1..N
Cell == BOOLEAN

\* ----- Helper definitions -----
Neighbors(p) ==
  LET i == p[1] IN
  LET j == p[2] IN
  { <<i + di, j + dj>> :
        di \in {-1,0,1} /\ dj \in {-1,0,1} /\
        (di # 0 \/ dj # 0) /\ 
        1 <= i + di /\ i + di <= N /\ 
        1 <= j + dj /\ j + dj <= N }

LiveNeighborsCount(p) ==
  Cardinality({ q \in Neighbors(p) : grid[q] })

\* ----- Initial state -----
Init ==
  /\ grid \in [CellPos X CellPos -> Cell]
  /\ \A p \in CellPos X CellPos : grid[p] \in {TRUE, FALSE}

\* ----- Next-state relation -----
Next ==
  /\ grid' \in [CellPos X CellPos -> Cell]
  /\ \A p \in CellPos X CellPos :
        LET cnt == LiveNeighborsCount(p) IN
        IF grid[p] = TRUE THEN
           (* Live cell survives with 2 or 3 live neighbors *)
           grid'[p] = (cnt = 2 \/ cnt = 3)
        ELSE
           (* Dead cell becomes alive with exactly 3 live neighbors *)
           grid'[p] = (cnt = 3)

\* ----- Specification -----
Spec ==
  Init /\ [][Next]_grid

\* ----- Safety invariant (type correctness) -----
TypeOK ==
  grid \in [CellPos X CellPos -> Cell]

\* ----- Theorems (optional, for completeness) -----
THEOREM SpecImpliesTypeOK ==
  Spec => []TypeOK

====