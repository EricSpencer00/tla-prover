---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLE grid

(*-------------------------------------------------------------------*)
(* Set of all positions on the N×N grid *)
Pos == 1..N X 1..N

(* Offsets used to enumerate neighbor coordinates *)
Offsets == {-1, 0, 1}

(* Absolute value *)
Abs(x) == IF x >= 0 THEN x ELSE -x

(* The eight neighboring positions of a cell p (within the grid) *)
Neighbors(p) ==
  LET i == p[1] IN
  LET j == p[2] IN
    { <<i + di, j + dj>> :
        di \in Offsets /\ dj \in Offsets /\
        ~(di = 0 /\ dj = 0) /\                     \* not the cell itself
        <<i + di, j + dj>> \in Pos }               \* stay inside the grid

(* Number of live neighbours of cell p *)
Count(p) == Cardinality({ q \in Pos : q \in Neighbors(p) /\ grid[q] })

(*-------------------------------------------------------------------*)
(* Initial state: each cell may be alive (TRUE) or dead (FALSE) *)
Init == grid \in [Pos -> BOOLEAN]

(* One synchronous update of the whole grid *)
Next ==
  /\ grid' = [p \in Pos |-> 
        LET cnt == Count(p) IN
          IF (grid[p] /\ (cnt = 2 \/ cnt = 3)) \/ (~grid[p] /\ cnt = 3)
          THEN TRUE
          ELSE FALSE
     ]

(* Specification *)
Spec == Init /\ [][Next]_grid

(* Type invariant *)
TypeOK == grid \in [Pos -> BOOLEAN]

====