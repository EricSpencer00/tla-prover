----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* The domain of the board positions *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* Initial state: any assignment of TRUE/FALSE to each position is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Helper that safely returns FALSE for out‑of‑bounds coordinates *)
CellValue(p) == IF p \in Pos THEN grid[p] ELSE FALSE

(* Number of live neighbours around a position p *)
score(p) == 
  LET nbrs == {<<dx, dy>> : dx \in -1..1, dy \in -1..1, (dx # 0) \/ (dy # 0)} 
  IN  Cardinality({q \in Pos : 
        /\ q # p
        /\ q \in {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
        /\ grid[q] = TRUE})

(* Evolution step of Conway's Game of Life *)
Next == 
  /\ grid' = [p \in Pos |-> 
        IF /\ grid[p] = TRUE /\ score(p) \in {2,3}
           \/ grid[p] = FALSE /\ score(p) = 3
        THEN TRUE 
        ELSE FALSE]

(* Full temporal specification *)
Spec == Init /\ [][Next]_<<grid>>

(* Type invariant: grid must always be a total mapping from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================