---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

(* ------------------------------------------------------------------------ *)
(* Domain of positions on the N x N board                                    *)
Pos == {<<x, y>> : x, y \in 1..N}

(* ------------------------------------------------------------------------ *)
(* Types and helper definitions                                               *)
vars == <<grid>>
TypeOK == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------ *)
(* Helper to compute the sum of a function over a finite set                   *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* ------------------------------------------------------------------------ *)
(* Scoring function: number of live neighbours of a position                 *)
sc[<<x, y>> \in (0 .. N+1) \X (0 .. N+1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

score(p) ==
  LET nbrs == {<<dx, dy>> \in {-1,0,1} \X {-1,0,1} : <<dx, dy>> # <<0,0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* ------------------------------------------------------------------------ *)
(* Initial state: any assignment of dead/alive to each cell is allowed        *)
Init == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------ *)
(* Transition: standard Game of Life rules                                   *)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF (grid[p] /\ score(p) \in {2,3}) \/ (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

(* ------------------------------------------------------------------------ *)
(* Specification *)
Spec == Init /\ [][Next]_vars

====