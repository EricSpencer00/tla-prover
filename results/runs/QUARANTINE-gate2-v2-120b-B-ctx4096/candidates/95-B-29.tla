----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* N is a natural number *)
ASSUME N \in Nat

vars == grid

VARIABLES dummy \* dummy variable to avoid the empty-state warning

(* Recursive definition to sum a function over a finite set *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* All positions inside the board, using the more typical tuple notation *)
Pos == { <<x, y>> : x \in 1..N, y \in 1..N }

(* Type invariant: the grid is a function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function to compute the contribution of a neighbor position *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  IF \/ x = 0 \/ y = 0 \/ x > N \/ y > N
        THEN 0
        ELSE IF grid[<<x, y>>] THEN 1 ELSE 0

(* Number of live neighbours of a position p *)
score(p) ==
  LET nbrs == { <<dx, dy>> : dx \in {-1, 0, 1},
                           dy \in {-1, 0, 1},
                           (dx # 0) \/ (dy # 0) } \* exclude (0,0)
      points == { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs }
  IN Sum(sc, points)

(* Initial state: any Boolean assignment to all board cells *)
Init == /\ grid \in [Pos -> BOOLEAN]
        /\ dummy = 0

(* Transition: synchronous update of every cell according to Game of Life rules *)
Next ==
  /\ grid' = [p \in Pos |-> 
               IF (grid[p] /\ score(p) \in {2, 3}) \/
                  (~grid[p] /\ score(p) = 3)
               THEN TRUE
               ELSE FALSE]
  /\ dummy' = dummy

(* Full specification *)
Spec == Init /\ [][Next]_<<grid, dummy>>

=============================================================================