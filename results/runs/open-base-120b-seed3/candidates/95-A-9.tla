---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES grid

(*-------------------------------------------------------------------*)
(* The set of positions on the N-by-N grid                           *)
Pos == 1..N \X 1..N

(* The set of neighboring positions (up to eight) for a given cell  *)
NeighborSet(p) == { q \in Pos :
                     p # q /\ 
                     Abs(p[1] - q[1]) <= 1 /\ 
                     Abs(p[2] - q[2]) <= 1 }

(* Number of live neighbors of a cell                                 *)
Cnt(p) == Cardinality({ q \in NeighborSet(p) : grid[q] })

(*-------------------------------------------------------------------*)
(* Initial state: any mapping from positions to BOOLEAN               *)
Init == grid \in [Pos -> BOOLEAN]

(*-------------------------------------------------------------------*)
(* One step of the Game of Life                                         *)
Next ==
  \E grid' \in [Pos -> BOOLEAN] :
    /\ \A p \in Pos :
         grid'[p] = IF grid[p]
                      THEN (Cnt(p) = 2 \/ Cnt(p) = 3)
                      ELSE (Cnt(p) = 3)

(*-------------------------------------------------------------------*)
(* Specification                                                     *)
Spec == Init /\ [][Next]_grid

(*-------------------------------------------------------------------*)
(* Type invariant                                                    *)
TypeOK == grid \in [Pos -> BOOLEAN]

====