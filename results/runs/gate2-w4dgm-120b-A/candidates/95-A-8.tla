---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Grid == 1..N

\* The full board is a record: the tag "g" is the grid, a mapping from
\* positions to their boolean (alive/dead) value.
VARIABLES g

vars == << g >>

Tag == [g : [Grid \X Grid -> BOOLEAN]]

TypeOK == g \in [Grid \X Grid -> BOOLEAN]

Init ==
  /\ \E f \in [Grid \X Grid -> BOOLEAN] : g = f

\* Outside-the-grid cells are treated as dead (value zero) for neighbor counts.
Dead(v) == IF v \in Grid \X Grid THEN g[v] ELSE FALSE

LiveNeighbors(r, c) ==
  Cardinality(
    {w \in Grid \X Grid :
        w # <<r, c>> /\ \E dr \in {-1, 0, 1}, dc \in {-1, 0, 1} :
          (dr # 0 \/ dc # 0) /\ <<r + dr, c + dc>> = w /\ g[w]})

NextState ==
  [<<r, c>> \in Grid \X Grid |->
     CASE Dead(r, c) /\ LiveNeighbors(r, c) = 3 -> TRUE
          [] Dead(r, c) /\ LiveNeighbors(r, c) # 3 -> FALSE
          [] ~Dead(r, c) /\ LiveNeighbors(r, c) \in {2, 3} -> TRUE
          [] OTHER -> FALSE]

Next == g' = NextState

Spec == Init /\ [][Next]_vars

====