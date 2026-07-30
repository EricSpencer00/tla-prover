---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == 1 .. N

VARIABLES cells

vars == <<cells>>

\* The neighbor count is computed with the grid's boundary treated as dead: any
\* coordinate outside 1..N contributes zero to the count.
Nb(p, q) == IF p \in Positions /\ q \in Positions THEN cells[<<p, q>>] ELSE FALSE

NbrCount(r, c) ==
  Nb(r - 1, c - 1) + Nb(r - 1, c) + Nb(r - 1, c + 1)
  + Nb(r, c - 1) + Nb(r, c + 1)
  + Nb(r + 1, c - 1) + Nb(r + 1, c) + Nb(r + 1, c + 1)

TypeOK ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

Init ==
  /\ cells = [pos \in Positions \X Positions |-> CHOOSE b \in BOOLEAN : TRUE]

Next ==
  /\ cells' = [pos \in Positions \X Positions |->
       LET r == pos[1] IN LET c == pos[2] IN
         CASE NbrCount(r, c) = 3 : TRUE
              /\ cells[pos] = FALSE
         [] NbrCount(r, c) \in {2, 3} : cells[pos]
         [] OTHER : FALSE]
  /\ UNCHANGED << >>

Spec == Init /\ [][Next]_vars

====