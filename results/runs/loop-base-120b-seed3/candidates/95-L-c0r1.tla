---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLE grid

(*-----------------------------------------------------------------
  Definitions
-----------------------------------------------------------------*)
Cell == 1..N \X 1..N

(* Helper to compute the inclusive integer range around a coordinate *)
RowRange(r) == (r - 1) .. (r + 1)

Neighbors(c) == { p \in Cell :
                    p # c /\ 
                    p[1] \in RowRange(c[1]) /\ 
                    p[2] \in RowRange(c[2]) }

LiveNeighborCount(c) == Cardinality({ p \in Neighbors(c) : grid[p] })

(*-----------------------------------------------------------------
  Initial state: any assignment of booleans to the cells
-----------------------------------------------------------------*)
Init == 
    /\ grid \in [Cell -> BOOLEAN]

(*-----------------------------------------------------------------
  Next-state relation: simultaneous update of all cells
-----------------------------------------------------------------*)
Next == 
    /\ grid' = [c \in Cell |-> 
                  IF grid[c] 
                     THEN (LiveNeighborCount(c) = 2 \/ LiveNeighborCount(c) = 3)
                     ELSE (LiveNeighborCount(c) = 3)
               ]

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_grid

(*-----------------------------------------------------------------
  Invariant: type correctness
-----------------------------------------------------------------*)
TypeOK == grid \in [Cell -> BOOLEAN]

====