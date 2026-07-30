---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* The grid is a fixed N-by-N board. Positions are the pairs (i, j) with
\* both coordinates in 1..N. Outside the board lives the shadow region,
\* treated as always dead for neighbor counting.
Positions == 1..N

VARIABLES alive

vars == <<alive>>

\* The eight neighbor offsets of a cell (horizontal, vertical, diagonal).
NeighborOffsets == {{
  <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
  <<0, -1>>,            <<0, 1>>,
  <<1, -1>>,  <<1, 0>>, <<1, 1>>
}}

\* A cell lives at p = <<i, j>> if i and j are in range and alive[p] is true.
OnBoard(p) == (p[1] \in Positions) /\ (p[2] \in Positions)

\* Neighbors of p that lie inside the board.
Neighbors(p) ==
  {q \in Positions \X Positions : (q[1] - p[1], q[2] - p[2]) \in NeighborOffsets}

\* Live-neighbor count, treating off-board cells as dead.
LiveNeighbors(p) ==
  Cardinality({q \in Neighbors(p) : alive[q]})

\* Rule: a live cell with 2 or 3 live neighbors survives; a dead cell
\* with exactly 3 live neighbors is born; all others die.
NextState(p) ==
  (alive[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3))
  \/ (~alive[p] /\ LiveNeighbors(p) = 3)

TypeOK == alive \in [Positions \X Positions -> BOOLEAN]

Init ==
  \E f \in [Positions \X Positions -> BOOLEAN] : alive = f

\* The whole board updates at once; the neighbor counts are read from
\* the old board and written into the new one.
Tick ==
  alive' = [p \in Positions \X Positions |-> NextState(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

====