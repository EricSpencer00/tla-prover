---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

(* The set of all positions on the N×N board *)
Pos == 1..N \X 1..N

(* A neighbor is any distinct position at most one step away horizontally,
   vertically, or diagonally. Positions outside the board are never in Pos,
   so they are implicitly dead. *)
IsNeighbor(p, q) == (p # q) /\ (Abs(p[1] - q[1]) <= 1) /\ (Abs(p[2] - q[2]) <= 1)

(* Number of live neighbours of position p in the current grid *)
CountLive(p) == Cardinality({ q \in Pos : IsNeighbor(p, q) /\ grid[q] })

(* Type invariant: grid maps every position to a Boolean value *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Any assignment of Booleans to all positions is a possible initial state *)
Init == TypeOK

(* Simultaneous update of all cells according to the Game of Life rules *)
Next ==
  \A p \in Pos:
    grid'[p] =
      ( (grid[p] /\ (CountLive(p) = 2 \/ CountLive(p) = 3))
        \/ (~grid[p] /\ CountLive(p) = 3) )

(* Full specification: start in Init and repeatedly take Next steps *)
Spec == Init /\ [][Next]_<<grid>>

====