---- MODULE GameOfLife ----
EXTENDS Naturals

(* Conway's Game of Life: a cellular automaton on a square grid.  Each cell is   *)
(* either alive or dead.  From any configuration every cell is updated          *)
(* simultaneously: a live cell with two or three live neighbors survives, a     *)
(* dead cell with exactly three live neighbors becomes alive, and every other    *)
(* cell dies.  Cells outside the N-by-N grid are treated as dead.                *)

CONSTANT N

Positions == (1..N) \X (1 .. N)

Outside == { [x |-> 0, y |-> 0] }

VARIABLES cell

vars == <<cell>>

TypeOK ==
    /\ cell \in [Positions -> BOOLEAN]

\* A live cell's live neighbors (in-bounds cells only; out-of-grid cells are dead)
LiveNeighbors(p) ==
    LET nbs == [q \in Positions |-> IF cell[q] /\ (p.x - q.x) \in {-1, 0, 1} /\ (p.y - q.y) \in {-1, 0, 1} /\ ~(p.x = q.x /\ p.y = q.y) THEN 1 ELSE 0]
    IN nbs[Outside] + nbs[[x |-> p.x + 1, y |-> p.y ]] + nbs[[x |-> p.x - 1, y |-> p.y ]]
       + nbs[[x |-> p.x, y |-> p.y + 1]] + nbs[[x |-> p.x, y |-> p.y - 1]]
       + nbs[[x |-> p.x + 1, y |-> p.y + 1]] + nbs[[x |-> p.x - 1, y |-> p.y - 1]]
       + nbs[[x |-> p.x + 1, y |-> p.y - 1]] + nbs[[x |-> p.x - 1, y |-> p.y + 1]]

Init ==
    /\ cell \in [Positions -> BOOLEAN]

\* Simultaneous update: the next generation is computed from the current one.
Tick ==
    /\ cell' = [p \in Positions |-> (cell[p] /\ LiveNeighbors(p) \in {2, 3}) \/ (~cell[p] /\ LiveNeighbors(p) = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

====