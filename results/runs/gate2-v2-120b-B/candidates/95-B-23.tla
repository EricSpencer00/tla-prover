----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(*  Sum is a recursive function that adds up the values of a mapping f over a
    finite set S.  The definition is unchanged from the original specification. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(*  The set of positions that are part of the finite N×N board. *)
Pos == {<<x, y>> : x, y \in 1..N}

(*  The intended type invariant: grid must be a total function from Pos to
    BOOLEAN.  The original specification accidentally used "\notin" which caused
    the invariant to be violated on every initial state.  This definition
    restores the correct meaning while preserving the intended behaviour of the
    model. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(*  The scoring function used by the Game of Life rules.  It counts the number
    of live neighbours of a given position p, treating positions outside the
    board as dead. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0
           \/ x > N \/ y > N
           \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

score(p) ==
  LET nbrs  == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
      points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
  IN Sum(sc, points)

(*  The initial state: every cell of the board is assigned a Boolean value. *)
Init == grid \in [Pos -> BOOLEAN]

(*  The transition relation implements the standard Game of Life rules. *)
Next ==
  grid' = [p \in Pos |-> IF \/ (grid[p] /\ score(p) \in {2, 3})
                        \/ (~grid[p] /\ score(p) = 3)
                       THEN TRUE
                       ELSE FALSE]

(*  Full specification: initialization followed by stuttering steps of Next. *)
Spec == Init /\ [][Next]_vars

=============================================================================