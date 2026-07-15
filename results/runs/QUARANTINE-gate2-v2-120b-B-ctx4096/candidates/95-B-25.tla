----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANT N
VARIABLE grid

(* The size of the board must be a natural number *)
ASSUME N \in Nat

(* Alias for the state variable *)
vars == grid

(* Set of all positions on the board *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* Helper for summation over a finite set *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

(* The intended type invariant: grid maps each position to a BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Score contribution of a single neighbor (including off‑board cells) *)
sc[<<x, y>> \in (0 .. N+1) \X (0 .. N+1)] ==
  IF x = 0 \/ y = 0 \/ x > N \/ y > N THEN 0
  ELSE IF grid[<<x, y>>] THEN 1
  ELSE 0

(* Number of live neighbours of a position p *)
score(p) ==
  LET nbrs == {<<dx, dy>> : dx \in {-1,0,1}, dy \in {-1,0,1},
                <<dx, dy>> # <<0,0>>}
  IN  Sum(sc, {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs})

(* Initial state: all cells are dead, which satisfies the type invariant *)
Init == grid = [p \in Pos |-> FALSE]

(* Transition relation, identical to the original specification *)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF (grid[p] /\ score(p) \in {2,3}) \/ (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================