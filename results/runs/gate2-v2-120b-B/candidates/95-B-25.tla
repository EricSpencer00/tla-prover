----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N
VARIABLE grid

(* The set of all positions on the N×N board. *)
Pos == { [x |-> i, y |-> j] : i \in 1..N, j \in 1..N }

(* Type predicate for the whole state. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Score for a position p; 1 if the cell is alive, 0 otherwise. *)
sc[p \in (0..N+1) \X (0..N+1)] ==
  IF p \notin Pos \/ ~grid[p] THEN 0 ELSE 1

(* Number of alive cells in a set of positions. *)
Score(p) ==
  LET nbrs == { <<dx, dy>> : dx \in {-1,0,1}, dy \in {-1,0,1},
                <<dx, dy>> # <<0,0>> } IN
  LET points == { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs } IN
  \A q \in points : q \in Pos => sc[q] = 1
  \* The above ensures we only count points that are on the board.

Init ==
  /\ grid \in [Pos -> BOOLEAN]
  /\ TypeOK

Next ==
  /\ grid' = [p \in Pos |-> 
        IF \/ (grid[p] /\ Score(p) \in {2,3})
           \/ (~grid[p] /\ Score(p) = 3)
        THEN TRUE
        ELSE FALSE]
  /\ TypeOK

vars == <<grid>>

Spec == Init /\ [][Next]_vars

=============================================================================