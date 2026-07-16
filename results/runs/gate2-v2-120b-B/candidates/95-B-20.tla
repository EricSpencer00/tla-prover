---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N
VARIABLE grid

(* The grid is a function from each valid position to a Boolean value. *)
vars == <<grid>>

Pos == { <<x, y>> : x \in 1..N, y \in 1..N }

(* ------------------------------------------------------------------------- *)
(* Helper definition for summing over a finite set of positions.              *)
(* ------------------------------------------------------------------------- *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

(* ------------------------------------------------------------------------- *)
(* The score of a position is the number of live neighbours.                *)
(* ------------------------------------------------------------------------- *)
nbrs == { <<dx, dy>> : dx \in -1..1, dy \in -1..1, <<dx, dy>> # <<0, 0>> }

sc(p) ==
    LET points == { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs }
    IN
        IF \A q \in points : q \in Pos /\ grid[q] THEN 1
        ELSE 0

score(p) == Sum(sc, { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs })

(* ------------------------------------------------------------------------- *)
(* Initialization: any Boolean assignment to the grid is allowed.            *)
(* ------------------------------------------------------------------------- *)
Init == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------- *)
(* State transition: standard Game of Life rules.                            *)
(* ------------------------------------------------------------------------- *)
Next ==
    /\ grid' = [p \in Pos |-> 
                IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Invariant that checks the type of the grid.                                 *)
(* ------------------------------------------------------------------------- *)
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================