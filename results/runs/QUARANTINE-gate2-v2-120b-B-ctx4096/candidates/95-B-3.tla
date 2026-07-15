---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

vars == grid

(* Recursive sum over a finite set of positions, using a function that maps
   each position to a natural number. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

(* The set of all valid cell positions on the N×N board. *)
Pos == { <<x, y>> : x, y \in 1..N }

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)

(* The original specification required the grid to **not** be a function
   from Pos to BOOLEAN, which is the opposite of the intended type
   constraint.  The corrected invariant states that every entry of the
   grid is a Boolean value, i.e., the grid *is* a function from Pos to
   BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* ----------------------------------------------------------------------
   Scoring (number of live neighbours) for a given position
   ---------------------------------------------------------------------- *)

(* For a coordinate outside the board we assign a score of 0; otherwise we
   count the number of live neighbours. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
    CASE \/ x = 0 \/ y = 0
           \/ x > N \/ y > N
         \/ ~grid[<<x, y>>] -> 0
         [] OTHER -> 1

(* Number of live neighbours around position p. *)
score(p) ==
    LET nbrs  == { <<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>> }
        points == { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs }
    IN Sum(sc, points)

(* ----------------------------------------------------------------------
   Initialization and transition
   ---------------------------------------------------------------------- *)

(* The initial state may be any Boolean assignment to the board. *)
Init == grid \in [Pos -> BOOLEAN]

(* Classic Game of Life update rule. *)
Next ==
    grid' = [p \in Pos |->
                IF \/ (grid[p] /\ score(p) \in {2, 3})
                   \/ (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

====