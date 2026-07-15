----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* Recursive sum of function values over a finite set *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE
        LET x == CHOOSE x \in S : TRUE
        IN f[x] + Sum(f, S \ {x})

Pos == {<<x, y>> : x, y \in 1..N}

(* The intended type invariant: grid maps each position in Pos to a Boolean. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Neighborhood points for a given position *)
nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}

(* Cell score: number of live neighbours (including a thin border of dead cells) *)
sc[<<x, y>> \in (0 .. N+1) \X (0 .. N+1)] ==
    IF x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] THEN 0
    ELSE 1

score(p) ==
    LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
    IN Sum(sc, points)

Init == grid \in [Pos -> BOOLEAN]

Next ==
    grid' = [p \in Pos |-> 
                IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================