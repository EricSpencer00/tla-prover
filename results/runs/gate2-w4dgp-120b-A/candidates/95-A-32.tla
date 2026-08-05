---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* A Conway's Life grid: the value at each position is true iff that cell is alive.
VARIABLES alive

Grid == 1..N

\* Neighbor positions: the eight adjacent positions in the Moore neighborhood, expressed
\* as offsets relative to a cell's (row, col) coordinate.
NeighborOffsets ==
  {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>, <<0, -1>>, <<0, 1>>, <<1, -1>>, <<1, 0>>, <<1, 1>>}

\* A neighbor of (r, c) is inside the grid iff its coordinates stay within 1..N.
Inside(r, c) == r >= 1 /\ r <= N /\ c >= 1 /\ c <= N

\* Count the live neighbors of a cell at (r, c); neighbors outside the grid contribute zero.
\* The count is bounded by 8, which is a concrete bound derived from the fixed neighborhood
\* size, so this bounded sum is a safe, well-founded way to compute it in TLC.
NeighborsAlive(r, c) ==
  LET f[Q \in SUBSET (1..N \X 1..N)] ==
    IF Q = {} THEN 0
    ELSE LET x == CHOOSE y \in Q : TRUE IN (IF alive[x] THEN 1 ELSE 0) + f[Q \ {x}]
  IN
    LET S == {<<r + dr, c + dc>> : <<dr, dc>> \in NeighborOffsets}
    IN f[S \cap (1..N \X 1..N)]

TypeOK == alive \in [Grid \X Grid -> BOOLEAN]

Init ==
  /\ alive = [p \in Grid \X Grid |-> CHOOSE v \in BOOLEAN : TRUE]

\* A live cell survives with two or three live neighbors; a dead cell becomes alive
\* with exactly three live neighbors; otherwise the cell dies.
Tick ==
  /\ alive' = [p \in Grid \X Grid |->
                 LET n == NeighborsAlive(p[1], p[2])
                 IN IF alive[p] THEN (n = 2 \/ n = 3) ELSE (n = 3)]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_alive

====