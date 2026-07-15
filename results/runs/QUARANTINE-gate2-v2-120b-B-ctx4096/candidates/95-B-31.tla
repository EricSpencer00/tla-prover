---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

(* The set of valid positions on the N×N board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid must be a total function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper to compute the sum of a function f over a finite set S *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Neighbor offsets (excluding the zero offset) *)
NbrOffsets == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}

(* Score contribution of a single cell p (whether it is alive or dead) *)
sc[p \in (0 .. N+1) \X (0 .. N+1)] ==
  IF p \notin Pos THEN 0
  ELSE IF ~grid[p] THEN 0
  ELSE 1

(* Number of live neighbors of position p *)
score(p) ==
  LET nbrs == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in NbrOffsets}
  IN Sum(sc, nbrs)

(* Initial state: any assignment of alive/dead to each cell in Pos *)
Init == grid \in [Pos -> BOOLEAN]

(* One evolution step of Conway's Game of Life *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

(* Full specification *)
Spec == Init /\ [][Next]_<<grid>>

====