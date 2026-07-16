---- MODULE GameOfLife ----
EXTENDS Integers, TLC

CONSTANT N
VARIABLE grid

(* The constant N must be a natural number. *)
ASSUME N \in Nat

(* The set of all positions on the NxN board. *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid is a total function from positions to Boolean. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Recursive sum over a finite set of positions, applying function f. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

(* Contribution of a single cell to the score of a position p. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  IF \/ x = 0 \/ y = 0
        \/ x > N \/ y > N
        \/ ~grid[<<x, y>>]
  THEN 0
  ELSE 1

(* Number of living neighbours of position p. *)
score(p) ==
  LET nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any assignment of Boolean values to the board. *)
Init == grid \in [Pos -> BOOLEAN]

(* One step of the Game of Life. *)
Next ==
  grid' = [p \in Pos |-> 
            IF \/ (grid[p] /\ score(p) \in {2, 3})
               \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_<<grid>>

====