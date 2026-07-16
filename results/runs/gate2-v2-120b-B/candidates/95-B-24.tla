---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE grid

(* Ensure N is a natural number *)
ASSUME N \in Nat

(* The set of all valid positions on the board *)
Pos == { <<x, y>> : x \in 1..N, y \in 1..N }

(* Helper to compute the sum of a function over a finite set *)
RECURSIVE Sum(_,_)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE IN
      f[x] + Sum(f, S \ {x})

(* A predicate describing the intended type of the state variable.
   It asserts that grid is a total function from each position in Pos to a Boolean value. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* The contribution of a single cell to the score of a point.
   Cells outside the board are considered dead, contributing 0. *)
sc[<<x, y>> \in (0..N+1) \X (0..N+1)] ==
  IF x \in 0..N+1 /\ y \in 0..N+1 /\ (x \in 1..N /\ y \in 1..N)
     THEN IF grid[<<x, y>>] THEN 1 ELSE 0
     ELSE 0

(* The number of live neighbours of a point p. *)
score(p) ==
  LET nbrs == { <<dx, dy>> : dx \in {-1,0,1}, dy \in {-1,0,1}, <<dx, dy>> # <<0,0>> } IN
    Sum(
      (* for each neighbour position, return 1 if that neighbour is alive, 0 otherwise *)
      [q \in (0..N+1) \X (0..N+1) |-> IF q \in Pos /\ grid[q] THEN 1 ELSE 0],
      { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs }
    )

(* Initial state: every cell is dead. This satisfies TypeOK. *)
Init == grid = [p \in Pos |-> FALSE]

(* The Game of Life transition. *)
Next ==
  /\ grid' = [p \in Pos |->
        IF (grid[p] /\ score(p) \in {2, 3}) \/
           (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

(* Full specification *)
Spec == Init /\ [][Next]_<<grid>>

====