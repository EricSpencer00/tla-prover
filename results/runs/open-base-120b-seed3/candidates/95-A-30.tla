---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE grid

Pos == 1 .. N

(* Offsets for the eight neighboring cells *)
NeighborOffsets == { <<dx, dy>> : dx \in -1 .. 1, dy \in -1 .. 1,
                      ~(dx = 0 /\ dy = 0) }

(* Number of alive neighbors of cell (i,j) *)
AliveNeighbors(i, j) ==
  LET ns == { <<i + dx, j + dy>> : <<dx, dy>> \in NeighborOffsets } IN
    Cardinality(
      { p \in ns :
          /\ p[1] \in Pos
          /\ p[2] \in Pos
          /\ grid[p[1]][p[2]] } )

(* Any mapping from positions to booleans is a possible initial state *)
Init ==
  grid \in [Pos -> [Pos -> BOOLEAN]]

(* Simultaneous update of the whole grid *)
Next ==
  \E newgrid \in [Pos -> [Pos -> BOOLEAN]] :
    /\ \A i \in Pos, j \in Pos :
         newgrid[i][j] =
           IF grid[i][j]
           THEN (AliveNeighbors(i, j) = 2 \/ AliveNeighbors(i, j) = 3)
           ELSE (AliveNeighbors(i, j) = 3)
    /\ grid' = newgrid

(* The full specification *)
Spec == Init /\ [][Next]_<<grid>>

(* Type invariant *)
TypeOK == grid \in [Pos -> [Pos -> BOOLEAN]]

====