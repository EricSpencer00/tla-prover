---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension, to be provided in the .cfg

(* ------------------------------------------------------------------- *)
(* State variable: mapping each position (i,j) with 1 <= i,j <= N to a   *)
(* boolean indicating whether the cell is alive (TRUE) or dead (FALSE) *)
(* ------------------------------------------------------------------- *)
VARIABLE grid

(* ------------------------------------------------------------------- *)
(* Helper definitions                                                  *)
(* ------------------------------------------------------------------- *)
Pos == 1..N

Coords == {i \in Pos, j \in Pos}

(* The set of all possible neighbor positions, including those outside *)
(* the grid.  These are filtered later.                                 *)
NeighborOffsets == {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,            << 0, 1>>,
    << 1, -1>>, << 1, 0>>, << 1, 1>>
}

(* Given a coordinate <<i, j>>, return the set of its neighbor coordinates *)
Neighbors(coord) ==
    LET i == coord[1] IN
    LET j == coord[2] IN
    { <<i+di, j+dj>> : <<di, dj>> \in NeighborOffsets }

(* Count live neighbors, treating any coordinate outside the grid as dead *)
LiveNeighborCount(coord) ==
    Cardinality( { nbr \in Neighbors(coord) :
        /\ 1 <= nbr[1] /\ nbr[1] <= N
        /\ 1 <= nbr[2] /\ nbr[2] <= N
        /\ grid[nbr] = TRUE } )

(* ------------------------------------------------------------------- *)
(* Type invariant (helps TLC)                                          *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ grid \in [Coords -> BOOLEAN]

(* ------------------------------------------------------------------- *)
(* Initial state: each cell nondeterministically alive or dead          *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ grid \in [Coords -> BOOLEAN] \* any mapping of booleans
    /\ TypeOK

(* ------------------------------------------------------------------- *)
(* Deterministic transition (Tick)                                      *)
(* ------------------------------------------------------------------- *)
Next ==
    /\ grid' = [coord \in Coords |-> 
        LET n == LiveNeighborCount(coord) IN
        IF grid[coord] = TRUE THEN
            (n = 2) \/ (n = 3)      \* survive
        ELSE
            n = 3                    \* birth
    ]
    /\ UNCHANGED <<>> \* no other variables

(* ------------------------------------------------------------------- *)
(* Specification: initial condition and always-step transition           *)
(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<grid>>

(* ------------------------------------------------------------------- *)
(* Explicit naming of the components expected by the .cfg                *)
(* ------------------------------------------------------------------- *)
VARIABLES grid
INIT Init
NEXT Next
INVARIANT TypeOK
SPECIFICATION Spec

====