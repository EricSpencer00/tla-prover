----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* Domain of grid: all positions inside the N×N board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid maps every position to a Boolean value *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Recursive sum over a finite set of positions *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

(* Neighborhood offsets, excluding the zero offset *)
NbrOffsets == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}

(* Score of a position: number of live neighbours *)
score(p) ==
  LET nbrs == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in NbrOffsets}
  IN Cardinality({q \in nbrs : q \in Pos /\ grid[q]})

(* Initial state: any assignment of Boolean values to the board *)
Init == grid \in [Pos -> BOOLEAN]

(* Evolution rule of Conway's Game of Life *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_<<grid>>

=============================================================================